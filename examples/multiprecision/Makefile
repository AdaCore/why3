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

.PHONY: all clean extract plots

all: extract

clean:
	rm -rf build bench
	if test -f distrib/Makefile ; then make -C distrib clean ; fi

why3:
	make -C ../..

MLWFILES = $(addsuffix .mlw, mpz_div2exp mpz_mul2exp mpz_mul mpz_sub mpz_add mpz_getset mpz get_str base_info powm sqrtrem sqrt toom logical div mul sub add compare util)

build/extracted:
	mkdir -p build
	rm -f build/extracted
	$(WHY3) extract -D wmpn.drv -D c -L . --recursive --modular --interface -o build/ \
	  --debug c_no_error_msgs wmpn.mlw #$(MLWFILES)
	touch build/extracted

build/sqrtinit.h: sqrtinit.ml
	mkdir -p build
	ocaml sqrtinit.ml > build/sqrtinit.h

build/binverttab.h: binverttab.ml
	mkdir -p build
	ocaml binverttab.ml > build/binverttab.h

extract: build/extracted build/sqrtinit.h build/binverttab.h

CFILES = build/uint64gmp.c build/z.c build/zadd.c build/zsub.c build/zmul.c build/zmul2exp.c build/zdiv2exp.c build/set.c build/get_str.c build/baseinfo.c build/powm.c build/fxp.c build/sqrt.c build/sqrt1.c build/toom.c build/div.c build/logical.c build/aliaslogical.c build/mul.c build/subold.c build/sub.c build/sub_1.c build/addold.c build/add.c build/add_1.c build/compare.c build/util.c build/int32.c

build/tests: tests.c extract
	gcc $(CFLAGS) tests.c $(CFILES) -Irandom -lgmp -o build/tests

build/minitests: tests.c extract
	gcc $(CFLAGS) -DCOMPARE_MINI tests.c $(CFILES) -Irandom -Imini-gmp -o build/minitests

UPPER = $(shell echo $* | tr [:lower:] [:upper:])

build/why3%bench: tests.c extract
	gcc $(CFLAGS) -DTEST_WHY3 -DTEST_$(UPPER) tests.c $(CFILES) -Iinclude -Irandom -lgmp -o $@

build/lib%bench: tests.c distrib/libwmp.a
	gcc $(CFLAGS) -DTEST_LIB -DTEST_WHY3 -DTEST_$(UPPER) tests.c -Irandom -Idistrib -Ldistrib -lwmp -lgmp -o $@

build/gmp%bench: tests.c extract
	gcc $(CFLAGS) -DTEST_GMP -DTEST_$(UPPER) tests.c $(CFILES) -Iinclude -Irandom -lgmp -o $@

build/minigmp%bench: tests.c extract
	gcc $(CFLAGS) -DTEST_MINIGMP -DTEST_$(UPPER) tests.c $(CFILES) -Iinclude -Imini-gmp -Irandom -o $@

BENCHS = why3add why3mul why3toom why3div gmpadd gmpmul gmptoom gmpdiv minigmpadd minigmpmul minigmpdiv minigmptoom gmppowm why3powm

BENCHFILES = $(addprefix bench/, $(BENCHS))

$(BENCHFILES): bench/%: build/%bench
	mkdir -p bench
	$< > $@

plots: $(BENCHFILES)
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
