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
  GMPFLAGS = -march=native -O2 -fomit-frame-pointer
endif

CFLAGS = $(GMPFLAGS) -Wall -Wno-unused -g -std=c11

all: why3 extract

clean:
	rm -rf build

why3:
	make -C ../..

MLWFILES= $(addsuffix .mlw, powm sqrtrem sqrt toom logical div mul sub add compare util)

cfiles: why3
	mkdir -p build
	$(WHY3) extract -D wmpn.drv -D c -L . --recursive --modular --interface -o build/ \
	wmpn.mlw
	#$(MLWFILES)

build/sqrtinit.h: sqrtinit.ml
	mkdir -p build
	ocaml sqrtinit.ml > build/sqrtinit.h

build/binverttab.h: binverttab.ml
	mkdir -p build
	ocaml binverttab.ml > build/binverttab.h

extract: cfiles build/sqrtinit.h build/binverttab.h

CFILES = build/uint64gmp.c build/powm.c build/fxp.c build/sqrt.c build/sqrt1.c build/toom.c build/div.c build/logical.c build/mul.c build/sub.c build/add.c build/compare.c build/util.c build/int32.c

tests: extract
	gcc $(CFLAGS) tests.c $(CFILES) -Irandom -lgmp -o build/tests
	gcc $(CFLAGS) -DCOMPARE_MINI tests.c $(CFILES) -Irandom -Imini-gmp -o build/minitests
	./build/tests
	./build/minitests

bench-tests: extract
	gcc $(CFLAGS) tests.c $(CFILES) -Irandom -lgmp -o build/bench-tests

build/why3%bench: extract
	gcc $(CFLAGS) -DTEST_WHY3 -DTEST_`echo $* | tr [:lower:] [:upper:]` tests.c $(CFILES) -Iinclude -Irandom -lgmp -o $@

build/gmp%bench: extract
	gcc $(CFLAGS) -DTEST_GMP -DTEST_`echo $* | tr [:lower:] [:upper:]` tests.c $(CFILES) -Iinclude -Irandom -lgmp -o $@

build/minigmp%bench: extract
	gcc $(CFLAGS) -DTEST_MINIGMP -DTEST_`echo $* | tr [:lower:] [:upper:]` tests.c $(CFILES) -Iinclude -Imini-gmp -Irandom -o $@

alltests: tests build/why3addbench build/why3mulbench build/why3toombench build/why3divbench build/gmpaddbench build/gmpmulbench build/gmptoombench build/gmpdivbench build/minigmpaddbench build/minigmpmulbench build/minigmpdivbench build/minigmptoombench build/gmppowmbench build/why3powmbench

data: alltests
	mkdir -p bench
	./build/why3addbench > bench/why3add
	./build/why3mulbench > bench/why3mul
	./build/why3toombench > bench/why3toom
	./build/why3divbench > bench/why3div
	./build/why3powmbench > bench/why3powm
	./build/gmpaddbench > bench/gmpadd
	./build/gmpmulbench > bench/gmpmul
	./build/gmptoombench > bench/gmptoom
	./build/gmpdivbench > bench/gmpdiv
	./build/gmppowmbench > bench/gmppowm
	./build/minigmpaddbench > bench/minigmpadd
	./build/minigmpmulbench > bench/minigmpmul
	./build/minigmptoombench > bench/minigmptoom
	./build/minigmpdivbench > bench/minigmpdiv

plots: data
	make all -C plots

dist: extract
	mkdir -p distrib/lib
	touch distrib/ChangeLog
	cp build/*.c build/*.h distrib/lib/
	cd distrib; ./autogen.sh
	cd distrib; make distcheck

tests-dist:
	make -C distrib
	gcc $(CFLAGS) tests.c -DTEST_LIB -Irandom -Idistrib -lgmp -Ldistrib -lwmp -o build/disttests
	./build/disttests
