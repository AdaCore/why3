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

ifdef GMP_DIR
  GMPFLAGS = $(shell sed -n -e 's/^CFLAGS = \(.*\)/\1/p' $(GMP_DIR)/Makefile)
else
  GMPFLAGS = -O2 -pedantic -fomit-frame-pointer
endif

CFLAGS = $(GMPFLAGS) -Wall -Wno-unused-function -g -std=c11

all: why3 extract

clean:
	rm -rf build

why3:
	make -C ../..

dir:
	mkdir -p build

MLWFILES= $(addsuffix .mlw, sqrtrem sqrt toom logical div mul sub add compare util)

cfiles: why3 dir
	$(WHY3) extract -D wmpn.drv -D c -L . --recursive --modular --interface -o build/ \
	wmpn.mlw
	#$(MLWFILES)

extract: why3 dir cfiles

CFILES = build/uint64gmp.c build/fxp.c build/sqrt.c build/sqrt1.c build/toom.c build/div.c build/logical.c build/mul.c build/sub.c build/add.c build/compare.c build/util.c build/int32.c

tests: extract check-gmp
	gcc $(CFLAGS) tests.c $(CFILES) -Iinclude -I$(GMP_DIR) -Irandom -L$(GMP_LIB) -lgmp -o build/tests
	gcc $(CFLAGS) -DCOMPARE_MINI tests.c $(CFILES) -Iinclude -I$(GMP_DIR) -Irandom -Imini-gmp -o build/minitests
	./build/tests
	./build/minitests

bench-tests: extract
	gcc $(CFLAGS) tests.c $(CFILES) -Iinclude -Ibench-include -Irandom -lgmp -o build/bench-tests


build/why3%bench: extract check-gmp
	gcc $(CFLAGS) -DTEST_WHY3 -DTEST_`echo $* | tr [:lower:] [:upper:]` tests.c $(CFILES) -Iinclude -I$(GMP_DIR) -Irandom -L$(GMP_LIB) -lgmp -o $@

build/gmp%bench: extract check-gmp
	gcc $(CFLAGS) -DTEST_GMP -DTEST_`echo $* | tr [:lower:] [:upper:]` tests.c $(CFILES) -Iinclude -I$(GMP_DIR) -Irandom -L$(GMP_LIB) -lgmp -o $@

build/minigmp%bench: extract
	gcc $(CFLAGS) -DTEST_MINIGMP -DTEST_`echo $* | tr [:lower:] [:upper:]` tests.c $(CFILES) -Iinclude -I$(GMP_DIR) -Imini-gmp -Irandom -o $@

alltests: tests build/why3addbench build/why3mulbench build/why3toombench build/why3divbench build/gmpaddbench build/gmpmulbench build/gmptoombench build/gmpdivbench build/minigmpaddbench build/minigmpmulbench build/minigmpdivbench build/minigmptoombench

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
	./build/minigmpaddbench > bench/minigmpadd
	./build/minigmpmulbench > bench/minigmpmul
	./build/minigmptoombench > bench/minigmptoom
	./build/minigmpdivbench > bench/minigmpdiv

plots: data
	make all -C plots

check-gmp:
ifndef GMP_DIR
	$(error GMP_DIR is undefined)
endif
ifndef GMP_LIB
	$(error GMP_LIB is undefined)
endif
