CLANG_PATH=${HOME}/bin/llvm-3.8.0/build-nat/bin  #change to your path

SOURCES = sgxbounds.cpp
LIB_NAME = sgxbounds.so

LDFLAGS = $(shell $(CLANG_PATH)/llvm-config --ldflags)
CXXFLAGS = -ggdb3 -Wall -fno-rtti -fPIC -shared $(shell $(CLANG_PATH)/llvm-config --cxxflags)

all: $(LIB_NAME)

$(LIB_NAME): $(SOURCES)
	g++ $(CXXFLAGS) $(LDFLAGS) $^ -o $@

clean:
	rm -f $(LIB_NAME)

