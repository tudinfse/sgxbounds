//===----- sgxbounds.cpp - Bounds Checker in SGX transformation pass -----===//
//
//	 This pass adds less-memory-intensive bounds checking inside SGX enclaves.
//   It adds two bounds metadata: lower bound and upper bound (spatial safety).
//
//   Upper bound is stored inside the fat pointer itself: we assume x86-64 arch
//   and 32-bit enclaves occupying low 0-4GB of RAM. Thus, the current pointer
//   is stored in low 32 bits, and upper bound -- in high 32 bits.
//   NOTE: Since upper bound is stored jointly with the pointer, we must be
//         careful with overflowing pointer/integer arithmetic.
//
//   Lower bound is stored in 4 bytes right behind the allocated object.
//   To access it knowing the pointer, we extract the upper bound (which
//   points exactly to the lower bound) and memory-read at this address.
//   NOTE: Accessing lower bound requires one additional memory access, and thus
//         must be avoided. The assumption is that lower-bounds checks are rare
//         in real programs, and analysis pass can help removing these checks.
//
//   NOTE: The suggested approach is a mix of pointer- and object-based defense.
//         It does not allow narrowing of bounds as in MPX/SoftBound.
//
//   TODOs:
//     - OptSafeChecks optimization (priority HIGH):
//        - don't insert a check in visitMemInst() in safe cases
//        - fast path: AddressSanitizer::isSafeAccess() for global and stack vars
//            (see llvm-3.8.0/llvm/lib/Transforms/Instrumentation)
//
//     - OptGEPOverflowProtection optimization (priority HIGH):
//        - don't use extract/combine helpers in visitGEP() when it can be proven
//          no int overflow can happen in 32 high bits
//        - smth similar to AddressSanitizer::isSafeAccess() should be enough
//
//     - OptScalarEvolution optimization (priority HIGH):
//        - employ Scalar Evolution (powerful but expensive)
//        - (1) remove dominated checks inside one BB with the same ptr-base:
//              - leave only one, minimum lower-bound check
//              - leave only one, maximum upper-bound check
//        - (2) hoist checks outside of simple loops with unknown trip count:
//              - look for AddRecs with the same ptr-base
//              - if AddRec's step is positive (common-case), leave only upper-bound check
//              - if AddRec's step is negative, hoist bounds extract & upper-bound check
//                and leave only lower-bound check
//
//     - OptICmpExtraction optimization (priority low):
//        - don't use extract in visitICmp() because it's useless in most cases
//        - at least libcxx must have this optimization disabled (probably others?)
//
//     - OptAllocaInstrumentation optimization (priority low):
//        - remove previously inserted __sgxbounds_alloca() for those stack vars
//          which are proven to never be involved in ptr arithmetic
//          (however, LLVM mem2reg already kills all mem-related allocas -> useless?)
//
//     - OptTempSameCheck (priority low):
//        - don't insert a check (createCheck) for ptr which is already covered
//          by a previous check on the same ptr
//        - already covered ptr must be *exactly* the same after stripPointerCasts()
//        - ASan and SafeCode use this opt so it must be useful
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "sgxbounds"

#include <llvm/Pass.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/InlineAsm.h>
#include <llvm/IR/Instruction.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Intrinsics.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/GlobalVariable.h>
#include <llvm/IR/Type.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/Support/Casting.h>
#include <llvm/IR/Dominators.h>
#include <llvm/ADT/DepthFirstIterator.h>
#include <llvm/ADT/SmallSet.h>
#include <llvm/Transforms/Utils/BasicBlockUtils.h>
#include <llvm/Support/CommandLine.h>
#include <llvm/IR/MDBuilder.h>
#include <llvm/IR/Metadata.h>
#include <llvm/IR/CallSite.h>
#include <llvm/Analysis/MemoryBuiltins.h>
#include <llvm/Analysis/TargetLibraryInfo.h>
#include <llvm/Analysis/ScalarEvolution.h>
#include <llvm/Analysis/ScalarEvolutionExpander.h>
#include <llvm/Analysis/ScalarEvolutionExpressions.h>
#include <llvm/Analysis/AssumptionCache.h>
#include <llvm/Analysis/LoopAccessAnalysis.h>
#include <llvm/Analysis/LoopInfo.h>
#include <llvm/Analysis/LoopIterator.h>
#include <llvm/Analysis/LoopPass.h>
#include <llvm/Analysis/ValueTracking.h>

#include <iostream>
#include <map>
#include <set>
#include <utility>
#include <tr1/memory>
#include <tr1/tuple>

#include "../include/common.h"

using namespace llvm;

static cl::opt<bool>
	NoCheckOnAll("no-check-all", cl::Optional, cl::init(false),
	cl::desc("Disable absolutely all checks"));

static cl::opt<bool>
	DumpSgx("dumpsgx", cl::Optional, cl::init(false),
	cl::desc("Dump the whole SGX module"));

static cl::opt<bool>
	EnableOpt("enable-opt", cl::Optional, cl::init(false),
	cl::desc("Enable optimizations"));
static cl::opt<bool>
	EnableOptPeephole("enable-opt-peephole", cl::Optional, cl::init(false),
	cl::desc("Peephole optimizations: (1) remove extracts right after combines"));
static cl::opt<bool>
	EnableOptSafeChecks("enable-opt-safe-checks", cl::Optional, cl::init(false),
	cl::desc("Do not insert a check (createCheck) in safe cases"));
static cl::opt<bool>
	EnableOptGEPOverflowProtection("enable-opt-gep-overflow-protection", cl::Optional, cl::init(false),
	cl::desc("Do not add extract/combine in GEPs if proven no int overflow can happen in 32 high bits"));
static cl::opt<bool>
	EnableOptScalarEvolution("enable-opt-scalar-evolution", cl::Optional, cl::init(false),
	cl::desc("Scalar evolution-based optimizations: (1) remove dominated checks, (2) hoist checks out of loops"));


namespace {

//===----------------------------------------------------------------------===//
typedef const SCEV* SCEVBasicBlockKey;
typedef std::pair<Instruction*, Instruction*> SCEVValuePair;
typedef std::pair<Instruction*, Instruction*> LowerUpperBound;

//===----------------------------------------------------------------------===//
class SgxBoundsPass {

	Module* M = nullptr;
	TargetLibraryInfo *TLI = nullptr;
	ScalarEvolution *SE = nullptr;

	SmallSet<Function*, 32> varargFuncs;
	DenseMap<Constant*, Constant*> globalUses;
	DenseMap<Instruction*, Instruction*> optimizedMemInsts;
	DenseMap<Instruction*, LowerUpperBound> boundsForInsts;

	Function* __sgxbounds_extract_ptrval;
	Function* __sgxbounds_extract_ptrval_vector2;
	Function* __sgxbounds_extract_ptrval_vector4;
	Function* __sgxbounds_extract_ubnd;
	Function* __sgxbounds_extract_ubnd_vector2;
	Function* __sgxbounds_extract_ubnd_vector4;
	Function* __sgxbounds_extract_lbnd;
	Function* __sgxbounds_combine_ptr;
	Function* __sgxbounds_combine_ptr_vector2;
	Function* __sgxbounds_combine_ptr_vector4;
	Function* __sgxbounds_check_allbnd;
	Function* __sgxbounds_check_ubnd;
	Function* __sgxbounds_check_lbnd;
	Function* __sgxbounds_alloca;
	Function* __sgxbounds_instrument_argv;
	Function* __sgxbounds_globals_init;
	Function* __sgxbounds_init;
	Function* __sgxbounds_highest_bound;
	Function* __sgxbounds_highest_bound_vector2;
	Function* __sgxbounds_highest_bound_vector4;
	Function* __sgxbounds_check_funcptr;
	Function* __sgxbounds_assign_environ;


	void markNoLowerBoundCheck(Instruction* I) {
		I->setMetadata("sgxboundsnolbndcheck", MDNode::get(M->getContext(), {}));
	}
	void markLowerBoundCheck(Instruction* I) {
		I->setMetadata("sgxboundsnolbndcheck", nullptr);
	}
	bool checkNoLowerBoundCheck(Instruction* I) {
		return (I->getMetadata("sgxboundsnolbndcheck") != nullptr);
	}

	void markNoUpperBoundCheck(Instruction* I) {
		I->setMetadata("sgxboundsnoubndcheck", MDNode::get(M->getContext(), {}));
	}
	void markUpperBoundCheck(Instruction* I) {
		I->setMetadata("sgxboundsnoubndcheck", nullptr);
	}
	bool checkNoUpperBoundCheck(Instruction* I) {
		return (I->getMetadata("sgxboundsnoubndcheck") != nullptr);
	}

	void markNoOptimizeAway(Instruction* I) {
		I->setMetadata("sgxboundsnoremove", MDNode::get(M->getContext(), {}));
	}
	bool checkNoOptimizeAway(Instruction* I) {
		return (I->getMetadata("sgxboundsnoremove") != nullptr);
	}

	void markAsSafe(Instruction* I) {
		markNoLowerBoundCheck(I);
		markNoUpperBoundCheck(I);
	}
	bool checkIfSafe(Instruction* I) {
		return (checkNoLowerBoundCheck(I) && checkNoUpperBoundCheck(I));
	}

	bool isSafePtr(Value *ptr, uint64_t size) {
		// check if ptr is always inbounds with respect to its base object
		// e.g., it is a field access or an array access with constant inbounds index
		// NOTE: adapted from isSafeAccess from AddressSanitizer.cpp in LLVM
		ObjectSizeOffsetVisitor ObjSizeVis(M->getDataLayout(), TLI, M->getContext(), true);
		SizeOffsetType objSizeOffset = ObjSizeVis.compute(ptr);
		if (!ObjSizeVis.bothKnown(objSizeOffset)) return false;

		uint64_t objSize = objSizeOffset.first.getZExtValue();
		int64_t objOffset = objSizeOffset.second.getSExtValue();

		// Three checks are required to ensure safety:
		// . objOffset >= 0  (since the offset is given from the base ptr)
		// . objSize >= objOffset  (unsigned)
		// . objSize - objOffset >= size  (unsigned)
		return objOffset >= 0 && objSize >= uint64_t(objOffset) &&
			objSize - uint64_t(objOffset) >= size / 8;
	}

	int getMemPointerOperandIdx(Instruction* I) {
		switch (I->getOpcode()) {
		case Instruction::Load:
			return cast<LoadInst>(I)->getPointerOperandIndex();
		case Instruction::Store:
			return cast<StoreInst>(I)->getPointerOperandIndex();
		case Instruction::AtomicCmpXchg:
			return cast<AtomicCmpXchgInst>(I)->getPointerOperandIndex();
		case Instruction::AtomicRMW:
			return cast<AtomicRMWInst>(I)->getPointerOperandIndex();
		}
		return -1;
	}

	bool shouldInstrumentGlobal(GlobalVariable *G) {
		if (G->isThreadLocal()) return false;
		if (!G->hasInitializer()) return false;

		if (G->getName().startswith("llvm.")) return false;
		if (G->getName().startswith("__sgxbounds_dummy")) return false;

		Type *Ty = G->getValueType();
		if (!Ty->isSized()) return false;

		if (G->hasSection()) {
			StringRef Section(G->getSection());
			if (Section == "llvm.metadata") return false;
			if (Section.find("__llvm") != StringRef::npos || Section.find("__LLVM") != StringRef::npos) return false;
			if (Section.startswith(".preinit_array") ||
			    Section.startswith(".init_array") ||
			    Section.startswith(".fini_array") ||
			    Section.startswith(".CRT")) {
			  return false;
			}
		}

		return true;
	}

	GlobalVariable* instrumentGlobal(GlobalVariable* G) {
		IRBuilder<> IRB( M->getContext() );

		// create new global var: struct with G as first item, lbnd as second item
  		Type* bndTy = IRB.getInt32Ty();
	    StructType* newTy = StructType::get(G->getValueType(), bndTy, nullptr);
	    GlobalVariable* newG = new GlobalVariable(*M, newTy, false,
	    						G->getLinkage(), nullptr,
	                            "", G, G->getThreadLocalMode());
	    newG->copyAttributesFrom(G);

	    // init struct with G's initializer in first item, NULL in second item
	    // NOTE: second item (lbnd) is inited at runtime via __sgxbounds_init()
	    Constant* newInitializer = ConstantStruct::get(newTy, G->getInitializer(),
	                            Constant::getNullValue(bndTy), nullptr);
	    newG->setInitializer(newInitializer);

	    return newG;
	}

	bool isVAArgType(Type* Ty) {
		if (ArrayType* AT = dyn_cast<ArrayType>(Ty))
			return isVAArgType(AT->getArrayElementType());
		if (PointerType* PT = dyn_cast<PointerType>(Ty))
			return isVAArgType(PT->getPointerElementType());
		if (StructType* ST = dyn_cast<StructType>(Ty)) {
			if (ST->hasName() && ST->getName() == "struct.__va_list_tag")
				return true;
		}
		return false;
	}

	Value* createExtract(IRBuilder<>& IRB, Value* ptr) {
		assert(ptr->getType()->isPointerTy());

		Value* ptr8       = IRB.CreatePointerCast(ptr, IRB.getInt8PtrTy());
		CallInst* ptrval8 = IRB.CreateCall(__sgxbounds_extract_ptrval, ptr8);
		Value* ptrval     = IRB.CreatePointerCast(ptrval8, ptr->getType());

		markNoOptimizeAway(ptrval8);
		return ptrval;
	}

	Value* createCheck(IRBuilder<>& IRB, Value* ptr, Value* ptrval, Instruction* I) {
		if (NoCheckOnAll)
			return nullptr;

		if (IRB.GetInsertBlock() && IRB.GetInsertBlock()->getParent()) {
			Function* F = IRB.GetInsertBlock()->getParent();
			// in special case of being inside vararg functions, relax
			// security guarantees and provide no checks
			// TODO: this is a dirty hack around messy vararg LLVM implementation
			if (varargFuncs.count(F))
				return nullptr;
		}

		assert(ptr->getType()->isPointerTy());
		assert(ptrval->getType()->isPointerTy());

		unsigned size = ptr->getType()->getPointerElementType()->getPrimitiveSizeInBits() / 8;

		Value* valSize = IRB.getInt64(size);
		Value* ptrval8 = IRB.CreatePointerCast(ptrval, IRB.getInt8PtrTy());

		Instruction* lbnd = nullptr;
		Instruction* ubnd = nullptr;

		if (optimizedMemInsts.count(I) && boundsForInsts.count(optimizedMemInsts[I])) {
			// there is a dominating instruction which bounds we should use
			lbnd = boundsForInsts[optimizedMemInsts[I]].first;
			ubnd = boundsForInsts[optimizedMemInsts[I]].second;
		} else if (I->getName().startswith("dummyoptimizationload")) {
			// this is a dominating instruction, always extract bounds
			ubnd = IRB.CreateCall(__sgxbounds_extract_ubnd,	IRB.CreatePointerCast(ptr, IRB.getInt8PtrTy()));
			lbnd = IRB.CreateCall(__sgxbounds_extract_lbnd, ubnd);

			LowerUpperBound pair(lbnd, ubnd);
			boundsForInsts[I] = pair;
		}

		if (!checkNoUpperBoundCheck(I) && !ubnd) {
			// need to insert upper bound check and there is no dominating instruction
			ubnd = IRB.CreateCall(__sgxbounds_extract_ubnd,	IRB.CreatePointerCast(ptr, IRB.getInt8PtrTy()));
		}
		if (!checkNoLowerBoundCheck(I) && !lbnd) {
			// need to insert lower bound check and there is no dominating instruction
			if (!ubnd) {
				DEBUG(dbgs() << "[===WARNING===] Inserting lower-bound check but could not find upper-bound check for: " << *I << "\n");
				ubnd = IRB.CreateCall(__sgxbounds_extract_ubnd,	IRB.CreatePointerCast(ptr, IRB.getInt8PtrTy()));
			}
			lbnd = IRB.CreateCall(__sgxbounds_extract_lbnd, ubnd);
		}

		if (checkNoUpperBoundCheck(I))	ubnd = nullptr;
		if (checkNoLowerBoundCheck(I))	lbnd = nullptr;

		Value* accesstype = IRB.getInt32(SGXBOUNDS_DEFACCESS);
		if (isa<LoadInst>(I))  accesstype = IRB.getInt32(SGXBOUNDS_RDACCESS);
		if (isa<StoreInst>(I))  accesstype = IRB.getInt32(SGXBOUNDS_WRACCESS);
		if (isa<AtomicCmpXchgInst>(I) || isa<AtomicRMWInst>(I))  accesstype = IRB.getInt32(SGXBOUNDS_RDWRACCESS);

		Value* newptrval = nullptr;
		if (lbnd && ubnd)
			newptrval = IRB.CreateCall(__sgxbounds_check_allbnd, {ptrval8, valSize, lbnd, ubnd, accesstype});
		else if (ubnd)
			newptrval = IRB.CreateCall(__sgxbounds_check_ubnd, {ptrval8, valSize, ubnd, accesstype});
		else if (lbnd)
			newptrval = IRB.CreateCall(__sgxbounds_check_lbnd, {ptrval8, lbnd, accesstype});

		if (newptrval)
			newptrval = IRB.CreatePointerCast(newptrval, ptr->getType());
		return newptrval;
	}

	void visitMemIntrinsic(MemIntrinsic *MI) {
		// replace llvm.memset/memmove/memcpy intrinsics via regular libc functions
	  IRBuilder<> IRB(MI);
	  if (isa<MemTransferInst>(MI)) {
	    IRB.CreateCall(
	        isa<MemMoveInst>(MI) ? M->getFunction("__sgxbound_memmove") : M->getFunction("__sgxbound_memcpy"),
	        {IRB.CreatePointerCast(MI->getOperand(0), IRB.getInt8PtrTy()),
	         IRB.CreatePointerCast(MI->getOperand(1), IRB.getInt8PtrTy()),
	         IRB.CreateIntCast(MI->getOperand(2), IRB.getInt64Ty(), false)});
	  } else if (isa<MemSetInst>(MI)) {
	    IRB.CreateCall(
	        M->getFunction("__sgxbound_memset"),
	        {IRB.CreatePointerCast(MI->getOperand(0), IRB.getInt8PtrTy()),
	         IRB.CreateIntCast(MI->getOperand(1), IRB.getInt32Ty(), false),
	         IRB.CreateIntCast(MI->getOperand(2), IRB.getInt64Ty(), false)});
	  }
	  MI->eraseFromParent();
	}

	Function* getExtractPtrvalBasedOnType(Type* inTy) {
		if (VectorType* Ty = dyn_cast<VectorType>(inTy))
			switch (Ty->getNumElements()) {
				case 2:  return __sgxbounds_extract_ptrval_vector2;
				case 4:  return __sgxbounds_extract_ptrval_vector4;
				default: assert(0 && "Found a vector-of-pointers of size not 2 nor 4!");
			}
		return __sgxbounds_extract_ptrval;
	}

	Function* getExtractUbndBasedOnType(Type* inTy) {
		if (VectorType* Ty = dyn_cast<VectorType>(inTy))
			switch (Ty->getNumElements()) {
				case 2:  return __sgxbounds_extract_ubnd_vector2;
				case 4:  return __sgxbounds_extract_ubnd_vector4;
				default: assert(0 && "Found a vector-of-pointers of size not 2 nor 4!");
			}
		return __sgxbounds_extract_ubnd;
	}

	Function* getCombinePtrBasedOnType(Type* inTy) {
		if (VectorType* Ty = dyn_cast<VectorType>(inTy))
			switch (Ty->getNumElements()) {
				case 2:  return __sgxbounds_combine_ptr_vector2;
				case 4:  return __sgxbounds_combine_ptr_vector4;
				default: assert(0 && "Found a vector-of-pointers of size not 2 nor 4!");
			}
		return __sgxbounds_combine_ptr;
	}

	Function* getHighestBoundBasedOnType(Type* inTy) {
		if (VectorType* Ty = dyn_cast<VectorType>(inTy))
			switch (Ty->getNumElements()) {
				case 2:  return __sgxbounds_highest_bound_vector2;
				case 4:  return __sgxbounds_highest_bound_vector4;
				default: assert(0 && "Found a vector-of-pointers of size not 2 nor 4!");
			}
		return __sgxbounds_highest_bound;
	}

	Type* getPtrTypeBasedOnType(IRBuilder<> &IRB, Type* inTy) {
		if (VectorType* Ty = dyn_cast<VectorType>(inTy))
			switch (Ty->getNumElements()) {
				case 2:  return VectorType::get(IRB.getInt64Ty(), 2);
				case 4:  return VectorType::get(IRB.getInt64Ty(), 4);
				default: assert(0 && "Found a vector-of-pointers of size not 2 nor 4!");
			}
		return IRB.getInt8PtrTy();
	}

	void visitGEP(GetElementPtrInst* GEP) {
		if (checkIfSafe(GEP))  return;

		// some optimizers operate on GEPs by internally lowering them into
		// more primitive integer expressions, producing pointers which
		// violate our assumptions; so ignore them
		if (GEP->getName().startswith("uglygep"))  return;

		IRBuilder<> IRB(GEP);

		// we must protect against int overflows ->
		//   extract ptr value, operate on it, and then combine back with ubnd
		Value* ptr  = GEP->getPointerOperand();
		if (BitCastInst* BCI = dyn_cast<BitCastInst>(ptr)) {
			if (BCI->getOperand(0)->getType()->isPointerTy())
				if (BCI->getOperand(0)->getType()->getPointerElementType()->isFunctionTy())
			    	DEBUG(dbgs() << "[===WARNING===] Found pointer arithmetic on function: " << *ptr << "\n");
		}

		Function* extract_ptrval = getExtractPtrvalBasedOnType(ptr->getType());
		Function* extract_ubnd   = getExtractUbndBasedOnType(ptr->getType());
		Function* combine_ptr    = getCombinePtrBasedOnType(ptr->getType());
		Type* ptrty              = getPtrTypeBasedOnType(IRB, ptr->getType());

		Value* casted    = IRB.CreateBitOrPointerCast(ptr, ptrty);
		Value* extracted = IRB.CreateCall(extract_ptrval, casted);
		Value* ubnd      = IRB.CreateCall(extract_ubnd,   casted);
		Value* ptrval    = IRB.CreateBitOrPointerCast(extracted, ptr->getType());

		GetElementPtrInst* newGEP = cast<GetElementPtrInst>(GEP->clone());
		newGEP->setOperand(0, ptrval);
		IRB.Insert(newGEP);

		Value* newVal = newGEP;
		newVal = IRB.CreateBitOrPointerCast(newVal, ptrty);
		newVal = IRB.CreateCall(combine_ptr, {newVal, ubnd});
		newVal = IRB.CreateBitOrPointerCast(newVal, GEP->getType());

		GEP->replaceAllUsesWith(newVal);
	    newVal->takeName(GEP);
	    GEP->eraseFromParent();
	}

	bool isPointerOriginally(Value* V) {
		if (V->getType()->isPointerTy())
			return true;
		if (isa<PtrToIntInst>(V))
			return true;
		if (V->getName().startswith("scevgep") || V->getName().startswith("uglygep"))
				return true;
		return false;
	}

	void visitICmp(ICmpInst* ICI) {
		// NOTE: useless? Reasoning:
		//   - ptr comparisons within the same object have the same ubnd
		//   - ptrs of different objects are correctly compared by their ubnds
		//   - NULL ptrs have an upbnd of NULL
		//
		// NOTE2: however, some libcxx code requires ptr comparison between
		//        different objects (thus many false positives emitted)
		//
		// NOTE3: comparison of extracted ptrs must be very efficient,
		//        since LLVM should optimize the whole code as comparison
		//        of 32-bit registers (e.g., ebx < ecx)
		IRBuilder<> IRB(ICI);

		for (unsigned opidx = 0; opidx < ICI->getNumOperands(); ++opidx) {
			Value* op = ICI->getOperand(opidx);
			if (!isPointerOriginally(op))
				continue;

			// ptr operand: must use only low bits for comparison
			Value* ptr8       = IRB.CreateBitOrPointerCast(op, IRB.getInt8PtrTy());
			CallInst* ptrval8 = IRB.CreateCall(__sgxbounds_extract_ptrval, ptr8);
			Value* ptrval     = IRB.CreateBitOrPointerCast(ptrval8, op->getType());

			markNoOptimizeAway(ptrval8);
			ICI->setOperand(opidx, ptrval);
		}
	}

	void visitAlloca(AllocaInst* AI) {
		// for vars allocated on stack, we use similar technique as with globals:
		//   int l;   -->   struct s {int l; PTRTYPE lbnd}
		// unlike globals, stack vars are dynamic and thus can be inited with call
		// to __sgxbounds_alloca(&s.l, &s.lbnd)
		IRBuilder<> IRB(AI);

		if (AI->isArrayAllocation()) {
			// special case of array-sized stack vars, no way to represent them
			// with struct type as above, so currently use dummy bounds
			// TODO: do not use dummy bounds
	    	DEBUG(dbgs() << "[===WARNING===] Found array-sized alloca: " << *AI << "\n");

			AllocaInst* newAI = IRB.CreateAlloca(AI->getAllocatedType(), AI->getArraySize());
			newAI->setAlignment(AI->getAlignment());

			CallInst* ubnd = IRB.CreateCall(__sgxbounds_highest_bound);
			Value* newVal  = cast<Instruction>(IRB.CreatePointerCast(newAI, IRB.getInt8PtrTy()));
			newVal = IRB.CreateCall(__sgxbounds_combine_ptr, {newVal, ubnd});
			newVal = IRB.CreatePointerCast(newVal, AI->getType());

			AI->replaceAllUsesWith(newVal);
		    newVal->takeName(AI);
		    AI->eraseFromParent();
			return;
		}

  		Type* bndTy = IRB.getInt32Ty();
	    StructType* newTy = StructType::get(AI->getAllocatedType(), bndTy, nullptr);
		AllocaInst* newAI = IRB.CreateAlloca(newTy);
		newAI->setAlignment(AI->getAlignment());

		Value* ubnd = nullptr;
		Value* newVal = newAI;

		ubnd = IRB.CreateGEP(newAI, {IRB.getInt32(0), IRB.getInt32(1)});
		ubnd = IRB.CreatePointerCast(ubnd, bndTy);
		newVal = IRB.CreatePointerCast(newVal, IRB.getInt8PtrTy());
		newVal = IRB.CreateCall(__sgxbounds_alloca, {newVal, ubnd});
		newVal = IRB.CreatePointerCast(newVal, AI->getType());

		AI->replaceAllUsesWith(newVal);
	    newVal->takeName(AI);
	    AI->eraseFromParent();
	}

	void visitMemInst(Instruction* MI) {
		IRBuilder<> IRB(MI);

		int ptrOperandIdx = getMemPointerOperandIdx(MI);
		assert(ptrOperandIdx >= 0 && "visitMemInst() expected Load/Store/AtomicCmpXchg/AtomicRMW!");
		Value* ptr = MI->getOperand(ptrOperandIdx);

		// check corner-case of assigning to `environ` -> need to rm all instrumentation in it
		if (StoreInst* SI = dyn_cast<StoreInst>(MI)) {
		 	if (M->getGlobalVariable("environ") == SI->getPointerOperand()->stripPointerCasts()) {
				Value* ptrval8 = IRB.CreateBitOrPointerCast(SI->getValueOperand(), IRB.getInt8PtrTy());
				IRB.CreateCall(__sgxbounds_assign_environ, {ptrval8});
				MI->eraseFromParent();
				return;
		 	}
		}

		// mem access on constant address -> no need to check
		if (isa<Constant>(ptr))
			return;

		Value* ptrval = createExtract(IRB, ptr);

		if (!checkIfSafe(MI)) {
			Value* newptrval = createCheck(IRB, ptr, ptrval, MI);
			if (newptrval)  ptrval = newptrval;
		}

		MI->setOperand(ptrOperandIdx, ptrval);
	}

	void visitCallInst(CallInst* CI) {
		IRBuilder<> IRB(CI);

		if (CI->isInlineAsm())
		    DEBUG(dbgs() << "[[WARNING]] FOUND INLINE ASM: " << *CI << "\n");

		if (!CI->isInlineAsm() && !CI->getCalledFunction()) {
			// TODO: function pointer call, should we do something?
			Value* ptrval8 = IRB.CreatePointerCast(CI->getCalledValue(), IRB.getInt8PtrTy());
			IRB.CreateCall(__sgxbounds_check_funcptr, {ptrval8});
			return;
		}

		if (CI->isInlineAsm()) {
			for (unsigned idxArgOp = 0; idxArgOp < CI->getNumArgOperands(); idxArgOp++) {
					Value* arg = CI->getArgOperand(idxArgOp);
					if (arg->getType()->isPointerTy()) {
						Value* argval = createExtract(IRB, arg);
						Value* newargval = createCheck(IRB, arg, argval, CI);
						if (newargval)  argval = newargval;
						CI->setArgOperand(idxArgOp, argval);
					} else if (arg->getType()->isVectorTy() ||
						arg->getType()->isAggregateType()) {
						errs() << "Found unsupported inline assembly with vectors/aggregates: " << *CI << "\n";
						assert(0 && "[[ERROR]] Cannot handle unsupported inline assembly!");
				}
			}
			return;
		}

		// special case of strlen: disallow backend to optimize it (by renaming)
		if (Function *F = CI->getCalledFunction()) {
			if (F->getName() == "strlen") {
			    Value* newCI = IRB.CreateCall(
			        M->getFunction("__sgxbound_strlen"),
			        {IRB.CreatePointerCast(CI->getOperand(0), IRB.getInt8PtrTy())});

				CI->replaceAllUsesWith(newCI);
			    newCI->takeName(CI);
			    CI->eraseFromParent();
				return;
			}
		}

		// special case of va_start and va_end intrinsics: required to uninstrument va_list
		if (Function *F = CI->getCalledFunction()) {
			if (F->isIntrinsic() &&
				(F->getName() == "llvm.va_start" || F->getName() == "llvm.va_end")) {
				Value* ptrval = createExtract(IRB, CI->getOperand(0));
				CI->setOperand(0, ptrval);
				return;
			}
		}

		// special case: look for funcs arguments that are passed "byval"
		// IR represents them as ptrs to aggregates, but in reality they are
		// passed by value (on x64, on stack) -> so uninstrument such "ptrs"
		for (unsigned idxArgOp = 0; idxArgOp < CI->getNumArgOperands(); idxArgOp++) {
			if (CI->paramHasAttr(idxArgOp+1, Attribute::ByVal)) {
				Value* arg = CI->getArgOperand(idxArgOp);
				Value* ptrval = createExtract(IRB, arg);
				CI->setArgOperand(idxArgOp, ptrval);
				CI->addAttribute(idxArgOp+1, Attribute::ByVal);
			}
		}
	}

	void visitInvokeInst(InvokeInst* CI) {
		IRBuilder<> IRB(CI);

		if (!CI->getCalledFunction()) {
			// TODO: function pointer call, should we do something?
			Value* ptrval8 = IRB.CreatePointerCast(CI->getCalledValue(), IRB.getInt8PtrTy());
			IRB.CreateCall(__sgxbounds_check_funcptr, {ptrval8});
			return;
		}

		// special case: look for funcs arguments that are passed "byval"
		// IR represents them as ptrs to aggregates, but in reality they are
		// passed by value (on x64, on stack) -> so uninstrument such "ptrs"
		for (unsigned idxArgOp = 0; idxArgOp < CI->getNumArgOperands(); idxArgOp++) {
			if (CI->paramHasAttr(idxArgOp+1, Attribute::ByVal)) {
				Value* arg = CI->getArgOperand(idxArgOp);
				Value* ptrval = createExtract(IRB, arg);
				CI->setArgOperand(idxArgOp, ptrval);
				CI->addAttribute(idxArgOp+1, Attribute::ByVal);
			}
		}
	}

	void visitPtrToIntInst(PtrToIntInst* PI) {
		// ptr -> int cast results in losing 32 high bits
		// NOTE: this is important for optimizations done on loops, for example
#if 0
		IRBuilder<> IRB(PI);
		Value* ptr = PI->getOperand(0);

		// funcptr -> int already has zero 32 high bits
		if (ptr->getType()->getPointerElementType()->isFunctionTy())  return;

		Function* extract_ptrval = getExtractPtrvalBasedOnType(ptr->getType());
		Type* ptrty              = getPtrTypeBasedOnType(IRB, ptr->getType());

		Value* casted    = IRB.CreateBitOrPointerCast(ptr, ptrty);
		Value* extracted = IRB.CreateCall(extract_ptrval, casted);
		Value* ptrval    = IRB.CreateBitOrPointerCast(extracted, ptr->getType());

		PI->setOperand(0, ptrval);
#endif
	}

	void visitIntToPtrInst(IntToPtrInst* II) {
		// int -> ptr results in putting highest_bound in 32 high bits
		// TODO: this compromises security, what could be done?!
#if 0
		IRBuilder<> IRB(II);

		// int -> funcptr must have zero 32 high bits
		if (II->getType()->getPointerElementType()->isFunctionTy())  return;

		IntToPtrInst* newII = cast<IntToPtrInst>(II->clone());
		IRB.Insert(newII);

		Function* highest_bound  = getHighestBoundBasedOnType(II->getType());
		Function* combine_ptr    = getCombinePtrBasedOnType(II->getType());
		Type* ptrty              = getPtrTypeBasedOnType(IRB, II->getType());

		CallInst* ubnd = IRB.CreateCall(highest_bound);
		Value* newVal = newII;
		newVal = IRB.CreateBitOrPointerCast(newVal, ptrty);
		newVal = IRB.CreateCall(combine_ptr, {newVal, ubnd});
		newVal = IRB.CreateBitOrPointerCast(newVal, II->getType());

		II->replaceAllUsesWith(newVal);
	    newVal->takeName(II);
	    II->eraseFromParent();
#endif
	}

	void initGlobalWithNewConstant(IRBuilder<> &IRB, GlobalVariable *G, SmallVector<Value*, 16> idxList, Constant* C) {
		if (ConstantExpr* CE = dyn_cast<ConstantExpr>(C)) {
			Value* ptr = IRB.CreateInBoundsGEP(G, idxList);
			IRB.CreateStore(CE, ptr);
			return;
		}
		if (isa<ConstantArray>(C) || isa<ConstantStruct>(C) || isa<ConstantVector>(C)) {
			for (unsigned opidx = 0; opidx < C->getNumOperands(); ++opidx) {
				Constant* op = cast<Constant>(C->getOperand(opidx));
				SmallVector<Value*, 16> subIdxList(idxList);
				subIdxList.push_back(IRB.getInt32(opidx));
				initGlobalWithNewConstant(IRB, G, subIdxList, op);
			}
		}
	}

	Constant* instrumentGlobalInConstant(Constant* C) {
		Constant* stripC = C->stripPointerCasts();

		if (globalUses.count(stripC)) {
			// it is global var, replace it with instrumented version

			// but if it's C++ EH typeinfo var, ignore it
			if (cast<GlobalVariable>(stripC)->getName().startswith("_ZTI"))
				return C;

			Constant* instrC = globalUses.find(stripC)->second;
			if (instrC->getType() != C->getType())
				instrC = ConstantExpr::getPointerCast(instrC, C->getType());
			return instrC;
		}

		std::vector<Constant*> newOps;
		int changed = 0;
		for (unsigned opidx = 0; opidx < C->getNumOperands(); ++opidx) {
			Constant* op = cast<Constant>(C->getOperand(opidx));
			Constant* newOp = instrumentGlobalInConstant(op);
			changed |= (newOp != op);

			if (newOp->getType() != op->getType())
				newOp = ConstantExpr::getPointerCast(newOp, op->getType());
			newOps.push_back(newOp);
		}
		if (!changed)  return C;

		if (ConstantExpr* CE = dyn_cast<ConstantExpr>(C))
			return CE->getWithOperands(newOps);
		if (ConstantArray* CA = dyn_cast<ConstantArray>(C))
			return ConstantArray::get(CA->getType(), newOps);
		if (ConstantStruct* CS = dyn_cast<ConstantStruct>(C))
			return ConstantStruct::get(CS->getType(), newOps);
		if (isa<ConstantVector>(C))
			return ConstantVector::get(newOps);

		assert(0 && "instGlobalInConstant() wanted to change Constant but did not find how");
		return nullptr;
	}

	void visitInst(Instruction* I) {
		// look for global vars as operands: if global is not
		// a load/store pointer, then it must be instrumented
		// with ubnd: g = g | (ubnd << 32)
		for (unsigned opidx = 0; opidx < I->getNumOperands(); ++opidx) {
			if (getMemPointerOperandIdx(I) == (int)opidx)  continue;

			Value* op = I->getOperand(opidx);
			if (!isa<Constant>(op))  continue;

			Constant* cop = cast<Constant>(op);
			Constant* newcop = instrumentGlobalInConstant(cop);
			if (newcop != cop)
				I->setOperand(opidx, newcop);
		}

		if (MemIntrinsic* MI = dyn_cast<MemIntrinsic>(I)) {
			// special case of mem intrinsics (memmove, memset, memcpy)
			visitMemIntrinsic(MI);
			return;
		}

		switch (I->getOpcode()) {

		case Instruction::GetElementPtr:
			visitGEP(cast<GetElementPtrInst>(I));
			break;

		case Instruction::ICmp:
			visitICmp(cast<ICmpInst>(I));
			break;

		case Instruction::Alloca:
			visitAlloca(cast<AllocaInst>(I));
			break;

		case Instruction::Load:
		case Instruction::Store:
		case Instruction::AtomicCmpXchg:
		case Instruction::AtomicRMW:
			visitMemInst(I);
			break;

		case Instruction::Call:
			visitCallInst(cast<CallInst>(I));
			break;

		case Instruction::Invoke:
			visitInvokeInst(cast<InvokeInst>(I));
			break;

		case Instruction::PtrToInt:
			visitPtrToIntInst(cast<PtrToIntInst>(I));
			break;

		case Instruction::IntToPtr:
			visitIntToPtrInst(cast<IntToPtrInst>(I));
			break;

		default:
			/* ignore other instructions */
			break;
		}
	}

#define REPLACEEXTRACTFUNC(NAME, NAME2, ARGNO) \
  { \
	if (CI->getCalledFunction() == NAME) { 									\
		Value* arg = CI->getArgOperand(0)->stripPointerCasts();  			\
		if (CallInst* CIArg = dyn_cast<CallInst>(arg)) {					\
			if (CIArg->getCalledFunction() == NAME2) {						\
				CI->replaceAllUsesWith(CIArg->getArgOperand(ARGNO));		\
				CIArg->takeName(CI);										\
				CI->eraseFromParent();										\
				return;														\
			}																\
		}																	\
	}																		\
  }

	void optimizeInst(Instruction* I) {
		if (!EnableOpt || !EnableOptPeephole)  return;
		if (checkNoOptimizeAway(I))  return;

		if (CallInst* CI = dyn_cast<CallInst>(I)) {
			REPLACEEXTRACTFUNC(__sgxbounds_extract_ptrval, __sgxbounds_combine_ptr, 0);
			REPLACEEXTRACTFUNC(__sgxbounds_extract_ubnd, __sgxbounds_combine_ptr, 1);

			REPLACEEXTRACTFUNC(__sgxbounds_extract_ptrval_vector2, __sgxbounds_combine_ptr_vector2, 0);
			REPLACEEXTRACTFUNC(__sgxbounds_extract_ubnd_vector2, __sgxbounds_combine_ptr_vector2, 1);

			REPLACEEXTRACTFUNC(__sgxbounds_extract_ptrval_vector4, __sgxbounds_combine_ptr_vector4, 0);
			REPLACEEXTRACTFUNC(__sgxbounds_extract_ubnd_vector4, __sgxbounds_combine_ptr_vector4, 1);
		}
	}

	// TODO: this analysis doesn't work yet, see https://groups.google.com/forum/#!topic/llvm-dev/GJ8gYohOrRA
	//       In short, isKnownPredicate() doesn't work as expected (always returns false)
	void analyzeScalarEvolutionInBasicBlock(DenseMap<SCEVBasicBlockKey, SCEVValuePair>& bbSCEVs, Instruction* I) {
		// remove dominated checks inside one BB with the same ptr-base:
		//   - leave only one, minimum lower-bound check
		//   - leave only one, maximum upper-bound check

		const SCEV* ptrSCEV = SE->getSCEV(I->getOperand(getMemPointerOperandIdx(I)));
		SCEVBasicBlockKey key(SE->getPointerBase(ptrSCEV));

		if (!bbSCEVs.count(key)) {
			// this I is the first value with this ptr base, add I
			errs() << "MARKED LOWER AND UPPER BOUND\n";
			markLowerBoundCheck(I);
			markUpperBoundCheck(I);
			SCEVValuePair pair(I, I);
			bbSCEVs[key] = pair;
			return;
		}

		// value with the same ptr base, compare them
		Instruction* currMinValueI = bbSCEVs[key].first;
		Instruction* currMaxValueI = bbSCEVs[key].second;

		const SCEV* currMinValueSCEV = SE->getSCEV(currMinValueI->getOperand(getMemPointerOperandIdx(I)));
		const SCEV* currMaxValueSCEV = SE->getSCEV(currMaxValueI->getOperand(getMemPointerOperandIdx(I)));

		errs() << "CHECKING LOWER BOUND:\n   " << *ptrSCEV << "\n   " << *currMinValueSCEV << "\n";

		if (SE->isKnownPredicate(ICmpInst::ICMP_SLT, ptrSCEV, currMinValueSCEV)) {
			// I loads/stores from ptr that is lower than currently memorized one ->
			// this I dominates previously memorized one, so replace with it
			errs() << "MARKED NEW LOWER BOUND\n";
			markNoLowerBoundCheck(currMinValueI);
			markLowerBoundCheck(I);
			currMinValueI = I;
		} else if (SE->isKnownPredicate(ICmpInst::ICMP_SGE, ptrSCEV, currMinValueSCEV)) {
			// I is dominated by previously memorized one, mark it as redundant
			errs() << "LEFT OLD LOWER BOUND\n";
			markNoLowerBoundCheck(I);
		}

		if (SE->isKnownPredicate(ICmpInst::ICMP_UGT, ptrSCEV, currMaxValueSCEV)) {
			// I loads/stores from ptr that is higher than currently memorized one ->
			// this I dominates previously memorized one, so replace with it
			errs() << "MARKED NEW UPPER BOUND\n";
			markNoUpperBoundCheck(currMaxValueI);
			markUpperBoundCheck(I);
			currMaxValueI = I;
		} else if (SE->isKnownPredicate(ICmpInst::ICMP_ULE, ptrSCEV, currMaxValueSCEV)) {
			// I is dominated by previously memorized one, mark it as redundant
			markNoUpperBoundCheck(I);
		}

		// we probably updated min and max for key, update in bbSCEVs
		SCEVValuePair pair(currMinValueI, currMaxValueI);
		bbSCEVs[key] = pair;
	}

	void analyzeScalarEvolutionInLoop(Instruction* I) {
		const SCEV* ptrSCEV = SE->getSCEV(I->getOperand(getMemPointerOperandIdx(I)));
		const SCEVAddRecExpr *AR = cast<SCEVAddRecExpr>(ptrSCEV);

		// we only work with expressions of form `A + B*x`
		if (!AR->isAffine())  return;
		// we only work with loops that have preheader (to put our optimized checks there)
		if (!AR->getLoop()->getLoopPreheader())  return;
		// we only work with memops that are guarantees to execute on each iteration
		if (!isGuaranteedToExecuteForEveryIteration(I, AR->getLoop()))  return;

		// insert dummy load from base-ptr in loop header: this will force
		// the following instrumentation to insert corresponding bounds check;
		// the load instruction itself will be optimized away later,
		// moreover, the lower-bound load will also be optimized away if unneeded
		BasicBlock* preheader = AR->getLoop()->getLoopPreheader();
		IRBuilder<> IRB(preheader->getTerminator());
		const DataLayout &DL = preheader->getModule()->getDataLayout();
		SCEVExpander Expander(*SE, DL, "loopscevs");

		// insert code for start check
		Value* expanded = Expander.expandCodeFor(AR->getStart(), nullptr, preheader->getTerminator());
		Instruction* startI = IRB.CreateLoad(expanded, "dummyoptimizationloadstart");

		// insert code for exit check if possible (works for simple loops with one exit)
		Instruction* exitI = nullptr;
        const SCEV *ExitValue = SE->getSCEVAtScope(AR, AR->getLoop()->getParentLoop());
        if (SE->isLoopInvariant(ExitValue, AR->getLoop())) {
			expanded = Expander.expandCodeFor(ExitValue, nullptr, preheader->getTerminator());
			exitI = IRB.CreateLoad(expanded, "dummyoptimizationloadexit");
			// exit check's existence implies no checks are needed inside loop
			markNoLowerBoundCheck(I);
			markNoUpperBoundCheck(I);
        }

		// memorize pair "this meminst -> headerload", the following instrumentation
		// will recognize such meminsts and use headerload's extracted lo/up bounds
		assert(optimizedMemInsts.count(I) == 0 && "SE-Loop optimization analyzed instruction more than once?!");
		optimizedMemInsts[I] = startI;

		if (SE->isKnownPositive(AR->getStepRecurrence(*SE))) {
			markNoLowerBoundCheck(I);
			markNoUpperBoundCheck(startI);
			if (exitI)  markNoLowerBoundCheck(exitI);
		}
		if (SE->isKnownNegative(AR->getStepRecurrence(*SE))) {
			markNoUpperBoundCheck(I);
			markNoLowerBoundCheck(startI);
			if (exitI)  markNoUpperBoundCheck(exitI);
		}
	}

	void visitMainFunc(Function* F) {
		Value* argv = nullptr;
		std::vector<Value*> argsVec;
		for (auto arg = F->arg_begin(), argend = F->arg_end(); arg != argend; ++arg) {
			argsVec.push_back(&*arg);
			if (arg->getArgNo() == 1) {
				// this is "argv" argument
				argv = &*arg;
			}
		}
		if (argv) {
			// some programs use old `main(int argc, char **argv, char **env)`,
			// we ignore `env` here
			if (argsVec.size() == 3)
				argsVec.pop_back();

			// call fat_argv = __sgxbounds_instrument_argv(argv) and
			// replace all "argv" uses with the new "fat_argv"
		    IRBuilder<> IRB(F->getEntryBlock().getFirstNonPHI());
			CallInst* fat_argv = IRB.CreateCall(__sgxbounds_instrument_argv, argsVec);
			assert(fat_argv->getType() == argv->getType());

			argv->replaceAllUsesWith(fat_argv);
			fat_argv->setArgOperand(1, argv); // hack to use original argv after replacement
		}
	}

public:

	SgxBoundsPass(Module *M, TargetLibraryInfo *TLI) {
		this->M   = M;
		this->TLI = TLI;
	}

	void setScalarEvolution(ScalarEvolution* SE) {
		this->SE  = SE;
	}

#define SGXBOUNDSFUNC(F)  (F->getName().startswith("__sgxbounds"))
#define GETSGXBOUNDSFUNC(NAME)  { if (F->getName().equals(#NAME)) NAME = F; }

	void findHelperFunc(Function *F) {
		if (!SGXBOUNDSFUNC(F))  return;
	 	F->setLinkage(GlobalValue::ExternalLinkage);

	 	GETSGXBOUNDSFUNC(__sgxbounds_extract_ptrval);
	 	GETSGXBOUNDSFUNC(__sgxbounds_extract_ptrval_vector2);
	 	GETSGXBOUNDSFUNC(__sgxbounds_extract_ptrval_vector4);
	 	GETSGXBOUNDSFUNC(__sgxbounds_extract_ubnd);
	 	GETSGXBOUNDSFUNC(__sgxbounds_extract_ubnd_vector2);
	 	GETSGXBOUNDSFUNC(__sgxbounds_extract_ubnd_vector4);
	 	GETSGXBOUNDSFUNC(__sgxbounds_extract_lbnd);
		GETSGXBOUNDSFUNC(__sgxbounds_combine_ptr);
		GETSGXBOUNDSFUNC(__sgxbounds_combine_ptr_vector2);
		GETSGXBOUNDSFUNC(__sgxbounds_combine_ptr_vector4);
		GETSGXBOUNDSFUNC(__sgxbounds_check_allbnd);
		GETSGXBOUNDSFUNC(__sgxbounds_check_ubnd);
		GETSGXBOUNDSFUNC(__sgxbounds_check_lbnd);
		GETSGXBOUNDSFUNC(__sgxbounds_alloca);
		GETSGXBOUNDSFUNC(__sgxbounds_instrument_argv);
		GETSGXBOUNDSFUNC(__sgxbounds_globals_init);
		GETSGXBOUNDSFUNC(__sgxbounds_init);
		GETSGXBOUNDSFUNC(__sgxbounds_highest_bound);
		GETSGXBOUNDSFUNC(__sgxbounds_highest_bound_vector2);
		GETSGXBOUNDSFUNC(__sgxbounds_highest_bound_vector4);
		GETSGXBOUNDSFUNC(__sgxbounds_check_funcptr);
		GETSGXBOUNDSFUNC(__sgxbounds_assign_environ);

		// remove all metadata from __sgxbounds_alloca() and all its instructions
		// NOTE: work around "!dbg attachment points at wrong subprogram" LLVM bug
		if (!F->getName().equals("__sgxbounds_alloca")) return;

		SmallVector<std::pair<unsigned, MDNode *>, 4> MDs;
		__sgxbounds_alloca->getAllMetadata(MDs);
		for (auto &MD : MDs)
			__sgxbounds_alloca->setMetadata(MD.first, nullptr);
		for (auto BB = __sgxbounds_alloca->begin(), BBend = __sgxbounds_alloca->end(); BB != BBend; ++BB) {
			for (auto I = BB->begin(); I != BB->end (); ) {
				auto nextIt = std::next(I);
				if (CallInst* CI = dyn_cast<CallInst>(I)) {
					if (CI->getCalledFunction() &&
						CI->getCalledFunction()->getName().startswith("llvm.dbg.")) {
							I->eraseFromParent();
							I = nextIt;
					}
				}
				I->getAllMetadata(MDs);
				for (auto &MD : MDs)
					I->setMetadata(MD.first, nullptr);
				I = nextIt;
			}
		}
	}

	void visitGlobals() {
		// for global vars, we replace them with struct {global, lbnd}, e.g.
		//   int g;   -->   struct s {int g; PTRTYPE lbnd}
		IRBuilder<> IRB( M->getContext() );

	    Value *idxglobal[2];
	    idxglobal[0] = IRB.getInt32(0);
	    idxglobal[1] = IRB.getInt32(0);
	    Value *idxlbnd[2];
	    idxlbnd[0] = IRB.getInt32(0);
	    idxlbnd[1] = IRB.getInt32(1);

		// push all globals into array Gs (this preliminary step is due
		// to eraseFromParent() and Initializers later in code)
		SmallVector<GlobalVariable*, 16> Gs;
		for (auto G = M->global_begin(), Gend = M->global_end(); G != Gend; ++G) {
			if (!shouldInstrumentGlobal(&*G)) continue;
			Gs.push_back(&*G);
		}

		size_t n = Gs.size();
	    SmallVector<Constant*, 16> Inits(n);
	    StructType* newGlobalsElemTy = StructType::get(IRB.getInt8PtrTy(), IRB.getInt8PtrTy(), nullptr);

		// instrument all globals
		SmallVector<GlobalVariable*, 16> newGs;
		for (size_t i = 0; i < n; i++) {
			GlobalVariable* G = Gs[i];
		    DEBUG(dbgs() << "Working on global var: " << G->getName() << "\n");

			GlobalVariable* newG = instrumentGlobal(G);
			newGs.push_back(newG);

        	Constant* newGval  = ConstantExpr::getGetElementPtr(newG->getValueType(), newG, idxglobal, true);
        	Constant* newGlbnd = ConstantExpr::getGetElementPtr(newG->getValueType(), newG, idxlbnd, true);

        	Constant* upBits = ConstantExpr::getShl(
        					ConstantExpr::getPointerCast(newGlbnd, IRB.getInt64Ty()),
        					IRB.getInt64(PTRSIZEBITS));
			Constant* loBits = ConstantExpr::getPointerCast(newGval, IRB.getInt64Ty());
			Constant* use = ConstantExpr::getIntToPtr(ConstantExpr::getOr(upBits, loBits), G->getType());

			// memorize [newG -> use] for later, we will instrument uses as follows:
			//   s.g  ->  (s.lbnd << 32) | s.g
			// note that in LLVM, newG and s.g (newGval) are equivalent after stripPointerCasts()
			globalUses[newG] = use;

			// all references to g are replaced by s.g; original g is erased
			G->replaceAllUsesWith(newGval);
		    newG->takeName(G);
		    G->eraseFromParent();

		    // memorize initializer pair (lbnd, ubnd) in Inits
		    Inits[i] = ConstantStruct::get(newGlobalsElemTy,
							ConstantExpr::getPointerCast(newGval, IRB.getInt8PtrTy()),
							ConstantExpr::getPointerCast(newGlbnd, IRB.getInt8PtrTy()),
							nullptr);
		}

	    IRBuilder<> IRBInit(__sgxbounds_init->getEntryBlock().getFirstNonPHI());

		// create helper array __sgxbounds_globals with filled up Inits
		ArrayType* newGlobalsTy = ArrayType::get(newGlobalsElemTy, n);
	    GlobalVariable* newGlobals = new GlobalVariable(
	        *M, newGlobalsTy, false, GlobalVariable::InternalLinkage,
	        ConstantArray::get(newGlobalsTy, Inits), "__sgxbounds_globals");

	    IRBInit.CreateCall(__sgxbounds_globals_init,
                   { IRBInit.CreatePointerCast(newGlobals, IRB.getInt8PtrTy()),
                    IRB.getInt64(n) });

	    // now the globals will be initialized at runtime via constructor
	    // __sgxbounds_init(): it will contain call to __sgxbounds_globals_init()
	    // which will go through all globals as defined in __sgxbounds_globals
	    // array and initialize corresponding s.lbnd

	    // check for special case of globals inited with other globals (e.g., a = {&b, &c})
	    // need to instrument such globals' initialization in __sgxbounds_init()
	    // NOTE: trying to instrument global's initializer results in `fatal error in backend`
	    //       because LLVM rightly cannot calculate arithmetic on unknown address (&g | bnd)
	    for (auto newGIt = newGs.begin(); newGIt != newGs.end(); newGIt++) {
	    	GlobalVariable* newG = *newGIt;
	    	if (newG->getInitializer()->isNullValue())  continue;

		    Constant* newInit = cast<Constant>(newG->getInitializer()->getOperand(0));
		    Constant* replacedInit = instrumentGlobalInConstant(newInit);
		    if (replacedInit != newInit) {
		    	// found global which is inited with other globals
		    	newG->setConstant(false);
		    	initGlobalWithNewConstant(IRBInit, newG, {IRB.getInt32(0), IRB.getInt32(0)}, replacedInit);
		    }
	    }
	}

	void visitFunc(Function* F) {
		if (SGXBOUNDSFUNC(F))  return;
	    DEBUG(dbgs() << "Working on function: " << F->getName() << "\n");

		if (F->getName() == "main") {
			visitMainFunc(F);
		}

		// check if function operates on special-case varargs (as ... or with va_list arg)
		if (F->isVarArg()) {
			DEBUG(dbgs() << "[===WARNING===] Found vararg function (...): " << F->getName() << "\n");
			varargFuncs.insert(F);
		}
		else {
			for (auto arg = F->arg_begin(), argend = F->arg_end(); arg != argend; ++arg) {
				if (isVAArgType(arg->getType())) {
					DEBUG(dbgs() << "[===WARNING===] Found vararg function (va_list): " << F->getName() << "\n");
					varargFuncs.insert(F);
					break;
				}

				// special case: look for funcs arguments that are passed "byval"
				// IR represents them as ptrs to aggregates, and our pass inserts
				// checks on dummy loads -> make such ptr use some bounds in IR
				Argument* Arg = &*arg;
				if (Arg->hasByValAttr()) {
				    IRBuilder<> IRB(F->getEntryBlock().getFirstNonPHI());
					CallInst* ubnd = IRB.CreateCall(__sgxbounds_highest_bound);
					Instruction* firstArg = cast<Instruction>(IRB.CreatePointerCast(Arg, IRB.getInt8PtrTy()));
					CallInst* call = IRB.CreateCall(__sgxbounds_combine_ptr, {firstArg, ubnd});
					Value* newArg = IRB.CreatePointerCast(call, Arg->getType());
					Arg->replaceAllUsesWith(newArg);
					firstArg->setOperand(0, Arg);  // hack to use original Arg after replacement
				}
			}
		}

		// main loop: iterate through all instructions
		for (auto BB = F->begin(), BBend = F->end(); BB != BBend; ++BB) {
			for (auto I = BB->begin(); I != BB->end (); ) {
				auto nextIt = std::next(I);
				visitInst(&*I);
				I = nextIt;
			}
		}

		// optimization loop: iterate through all instructions
		for (auto BB = F->begin(), BBend = F->end(); BB != BBend; ++BB) {
			for (auto I = BB->begin(); I != BB->end (); ) {
				auto nextIt = std::next(I);
				optimizeInst(&*I);
				I = nextIt;
			}
		}
	}

	void analyzeFunc(Function* F) {
		if (SGXBOUNDSFUNC(F))  return;

		DenseMap<SCEVBasicBlockKey, SCEVValuePair> bbSCEVs;

		for (auto BB = F->begin(), BBend = F->end(); BB != BBend; ++BB) {
			bbSCEVs.clear();	// map of dominated checks inside one BB

			for (auto II = BB->begin(); II != BB->end (); ++II) {
				Instruction* I = &*II;
				// mark safe memory operations
				if (isa<LoadInst>(I) || isa<StoreInst>(I) || isa<AtomicRMWInst>(I) || isa<AtomicCmpXchgInst>(I)) {
					Value* ptr = I->getOperand(getMemPointerOperandIdx(I));
					unsigned size = ptr->getType()->getPointerElementType()->getPrimitiveSizeInBits() / 8;

					if (EnableOpt && EnableOptSafeChecks) {
						if (isSafePtr(ptr, size))  markAsSafe(I);
					}

					if (EnableOpt && EnableOptScalarEvolution && !checkIfSafe(I)) {
						// employ Scalar Evolution on memop ptr
						if (static_cast<SCEVTypes>(SE->getSCEV(ptr)->getSCEVType()) == scAddRecExpr) {
							// loop-based
							analyzeScalarEvolutionInLoop(I);
						} else {
#if 0
							analyzeScalarEvolutionInBasicBlock(bbSCEVs, I);
#endif
						}
					}
				}

				// mark safe GEPs
				if (isa<GetElementPtrInst>(I)) {
					if (EnableOpt && EnableOptGEPOverflowProtection)
						if (isSafePtr(I, 0))  markAsSafe(I);
				}
			}
		}
	}

};

class SgxBoundsModule : public ModulePass {
	public:
	static char ID;

	SgxBoundsModule(): ModulePass(ID) { }

	virtual bool runOnModule(Module &M) {
		DEBUG(dbgs() << "[RUNNING PASS: sgxbounds]\n");

		TargetLibraryInfo *TLI = &getAnalysis<TargetLibraryInfoWrapperPass>().getTLI();
		SgxBoundsPass SgxBounds(&M, TLI);

		// 0. Prepare runtime for the pass
		for (auto F = M.begin(), Fend = M.end(); F != Fend; ++F) {
			if (F->isDeclaration())  continue;
			SgxBounds.findHelperFunc(&*F);
		}

		// 1. For each function, analyze its GEPs and mem accesses
		//    (this step adds `sgxboundssafe` metadata to safe instrs)
		for (auto F = M.begin(), Fend = M.end(); F != Fend; ++F) {
			if (F->isDeclaration())  continue;
			SgxBounds.setScalarEvolution(&getAnalysis<ScalarEvolutionWrapperPass>(*F).getSE());
			SgxBounds.analyzeFunc(&*F);
		}

		// 2. Change object layout for globals by adding 4-byte lower bound:
		//    (for dynamic objects, malloc wrapper will do it)
		//    (for function locals, we instrument `alloca` inst)
		SgxBounds.visitGlobals();

		// 3. For each function, instrument ptr uses and insert checks:
		for (auto F = M.begin(), Fend = M.end(); F != Fend; ++F) {
			if (F->isDeclaration())  continue;
			SgxBounds.visitFunc(&*F);
		}

		if (DumpSgx)
	    	DEBUG(dbgs() << "===== Module ===== " << *&M << "\n");

		// inform that we always modify a function
		return true;
	}

	virtual void getAnalysisUsage(AnalysisUsage& AU) const {
		AU.addRequired<ScalarEvolutionWrapperPass>();
	    AU.addRequired<TargetLibraryInfoWrapperPass>();
	}
};

char SgxBoundsModule::ID = 0;
static RegisterPass<SgxBoundsModule> X("sgxbounds", "SGX Bounds Pass");

}
