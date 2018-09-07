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

CFILES = build/uint64gmp.c build/toom.c build/div.c build/logical.c build/mul.c build/sub.c build/add.c build/compare.c build/util.c build/int32.c

tests: extract check-gmp
	gcc -O2 -Wall -Wno-unused-function -g -std=c11 -pedantic tests.c $(CFILES) -I$(GMP_DIR) -Irandom -L$(GMP_LIB) -fomit-frame-pointer -mtune=haswell -march=haswell -fno-tree-vectorize -lgmp -o build/tests
	gcc -O2 -Wall -Wno-unused-function -g -std=c11 -pedantic -DCOMPARE_MINI tests.c $(CFILES) -I$(GMP_DIR) -Irandom -Imini-gmp -fomit-frame-pointer -mtune=haswell -march=haswell -fno-tree-vectorize -o build/minitests
	./build/tests
	./build/minitests

bench-tests: extract
	gcc -O2 -Wall -Wno-unused-function -g -std=c11 tests.c $(CFILES) -Ibench-include -Irandom -fomit-frame-pointer -fno-tree-vectorize -lgmp -o build/bench-tests


build/why3%bench: extract check-gmp
	gcc -O3 -Wall -g -std=c11 -DTEST_WHY3 -DTEST_`echo $* | tr [:lower:] [:upper:]` tests.c $(CFILES) -I$(GMP_DIR) -Irandom -L$(GMP_LIB) -fomit-frame-pointer -mtune=haswell -march=haswell -fno-tree-vectorize -lgmp -o $@

build/gmp%bench: extract check-gmp
	gcc -O3 -Wall -g -std=c11 -DTEST_GMP -DTEST_`echo $* | tr [:lower:] [:upper:]` tests.c $(CFILES) -I$(GMP_DIR) -Irandom -L$(GMP_LIB) -fomit-frame-pointer -mtune=haswell -march=haswell -fno-tree-vectorize -lgmp -o $@

#build/minigmp%bench: extract
#	gcc -O3 -Wall -g -std=c11 -DTEST_MINIGMP -DTEST_`echo $* | tr [:lower:] [:upper:]` tests.c $(CFILES) -I$(GMP_DIR) -Irandom -fomit-frame-pointer -mtune=haswell -march=haswell -fno-tree-vectorize -o $@

alltests: tests build/why3addbench build/why3mulbench build/why3toombench build/why3divbench build/gmpaddbench build/gmpmulbench build/gmptoombench build/gmpdivbench #build/minigmpaddbench build/minigmpmulbench build/minigmpdivbench

data: alltests
	mkdir -p bench
	./build/why3addbench > bench/why3add
	./build/why3mulbench > bench/why3mul
	./build/why3toombench > bench/why3toom
	./build/why3divbench > bench/why3div
	./build/gmpaddbench > bench/gmpadd
	./build/gmpmulbench > bench/gmpmul
	./build/gmptoombench > bench/gmptoom
	./build/gmpdivbench > bench/gmpdiv
#	./build/minigmpaddbench > bench/minigmpadd
#	./build/minigmpmulbench > bench/minigmpmul
#	./build/minigmpdivbench > bench/minigmpdiv

plots: data
	make all -C plots

check-gmp:
ifndef GMP_DIR
	$(error GMP_DIR is undefined)
endif
ifndef GMP_LIB
	$(error GMP_LIB is undefined)
endif
