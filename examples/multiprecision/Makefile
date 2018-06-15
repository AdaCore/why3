BENCH ?= no

ifeq ($(BENCH),yes)
  WHY3=../../bin/why3.opt
else
  ifeq ($(BINDIR),)
    WHY3=why3
  else
    WHY3=$(BINDIR)/why3
  endif
endif

all: why3 extract

clean:
	rm -rf build

why3:
	make -C ../..

dir:
	mkdir -p build

cfiles: why3 dir
	$(WHY3) extract -D c -L . --recursive --modular --interface -o build/ wmpn.mlw

extract: why3 dir cfiles

CFILES = build/uint64gmp.c build/div.c build/logical.c build/mul.c build/sub.c build/add.c build/compare.c build/util.c  build/int32.c

tests: extract check-gmp
	gcc -O2 -Wall -Wno-unused-function -g -std=gnu99 tests.c $(CFILES) -I$(GMP_DIR) -L$(GMP_LIB) -fomit-frame-pointer -mtune=haswell -march=haswell -fno-tree-vectorize -lgmp -o build/tests
	gcc -O2 -Wall -Wno-unused-function -g -std=gnu99 -DCOMPARE_MINI tests.c $(CFILES) -I$(GMP_DIR) -fomit-frame-pointer -mtune=haswell -march=haswell -fno-tree-vectorize -o build/minitests
	./build/tests
	./build/minitests

bench-tests: extract
	gcc -O2 -Wall -g -std=gnu99 tests.c $(CFILES) -Ibench-include -fomit-frame-pointer -fno-tree-vectorize -lgmp -o build/bench-tests

check-gmp:
ifndef GMP_DIR
	$(error GMP_DIR is undefined)
endif
ifndef GMP_LIB
	$(error GMP_LIB is undefined)
endif
