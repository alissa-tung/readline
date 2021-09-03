default_target: all

LIB_PREFIX        ?= ${HOME}/.idris2/lib
CC                 = clang -O2 -g -Wall
CLANG_GEN_IDR_LIB  = clang -O2 -g -Wall -shared -fPIC

all: init fmt isocline readline doc test install

install: readline
	(idris2 --install readline.ipkg)
	(rm -rf ${LIB_PREFIX}/libisoclineidr.so)
	(cp ./libisoclineidr.so ${LIB_PREFIX}/)

clean:
	(idris2 --clean readline.ipkg)
	(cd ./rltest || exit && \
		idris2 --clean rltest.ipkg)
	(cd ./depends/isocline || exit && \
		make clean                   && \
		rm -rf CMakeCache.txt CMakeFiles Makefile cmake_install.cmake a.out)
	(rm -rf build libisoclineidr.so)

init:
	(cd ./depends/isocline && \
		git checkout idris)

fmt:
	(clang-format -i ./depends/isocline/src/idris.c)

doc:
	(idris2 --mkdoc readline.ipkg)

isocline:
	(cd ./depends/isocline || exit    && \
		cmake CMakeLists.txt            && \
		make all                        && \
		$(CLANG_GEN_IDR_LIB) ./src/idris.c \
			-o ../../libisoclineidr.so)

test: readline
	(cd ./rltest || exit && \
		idris2 --build rltest.ipkg)
	(cd ./rltest && \
		./build/exec/runtests idris2 --interactive --failure-file failures)

readline:
	(sed -i "s|__LIB_PREFIX__|${LIB_PREFIX}|g" ./src/Internal/Path.idr)
	(idris2 --build readline.ipkg)
