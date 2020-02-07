BENCH ?= no
OVERLAY ?= no

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
  CFLAGS = $(shell sed -n -e 's/^CFLAGS = \(.*\)/\1/p' $(GMP_DIR)/Makefile)
else
  CFLAGS = -march=native -O2 -fomit-frame-pointer
endif

ifdef GMP_LIB
  GMPFLAGS = -I$(GMP_LIB)/include -L$(GMP_LIB)/lib
endif

CFLAGS += -Wall -Wno-unused -g -std=c11 -Wno-pedantic

.PHONY: all clean extract plots benchs dist tests-dist

all: extract

clean:
	rm -rf build bench
	if test -f distrib/Makefile ; then make -C distrib clean ; fi

why3:
	make -C ../..

MLWFILES = $(addsuffix .mlw, mpz_div2exp mpz_mul2exp mpz_mul mpz_sub mpz_add mpz_getset mpz_cmp mpz get_str base_info powm sqrtrem sqrt toom logical div mul sub add compare util)

build/extracted: $(MLWFILES)
	mkdir -p build
	rm -f $@
	$(WHY3) extract -D wmpn.drv -D c -L . --recursive --modular --interface -o build/ \
	  --debug c_no_error_msgs wmpn.mlw #$(MLWFILES)
	touch $@

build/sqrtinit.h: sqrtinit.ml
	mkdir -p build
	ocaml sqrtinit.ml > build/sqrtinit.h

build/binverttab.h: binverttab.ml
	mkdir -p build
	ocaml binverttab.ml > build/binverttab.h

EXTRACTED = build/extracted build/sqrtinit.h build/binverttab.h

extract: $(EXTRACTED)

CFILES = zutil.c z.c zcmp.c zadd.c zsub.c zmul.c zmul2exp.c zdiv2exp.c set.c get_str.c baseinfo.c powm.c fxp.c sqrt.c sqrt1.c toom.c div.c logical.c aliaslogical.c mul_basecase.c sub.c sub_1.c add.c add_1.c compare.c util.c int32.c

ifneq ($(OVERLAY),gmp)
CFILES += mul.c addold.c subold.c
endif

gmp_INCLUDES = mul.h add.h sub.h
mini_INCLUDES = uint64gmp.h
no_INCLUDES =
INCLUDES = $($(OVERLAY)_INCLUDES)

build/libwmp.a: $(EXTRACTED)
	cd build; gcc $(CFLAGS) $(INCLUDES:%=-include ../overlays/%) -c $(CFILES)
	ar rcs $@ $(addprefix build/,$(CFILES:.c=.o))

build/tests: tests.c build/libwmp.a
	gcc $(CFLAGS) tests.c -Irandom -Lbuild -lm -lwmp -lgmp -o $@

build/minitests: tests.c build/libwmp.a
	gcc $(CFLAGS) -DCOMPARE_MINI tests.c -Irandom -Imini-gmp -Lbuild -lm -lwmp -o $@

UPPER = $(shell echo $* | tr [:lower:] [:upper:])

build/why3%bench: tests.c build/libwmp.a
	gcc $(CFLAGS) -DTEST_WHY3 -DTEST_$(UPPER) tests.c -Iinclude -Irandom -Lbuild -lm -lwmp -lgmp -o $@

build/lib%bench: tests.c distrib/libwmp.a
	gcc $(CFLAGS) -DTEST_LIB -DTEST_WHY3 -DTEST_$(UPPER) tests.c -Irandom -Idistrib -Ldistrib -lm -lwmp -lgmp -o $@

build/gmp%bench: tests.c build/libwmp.a
	gcc $(CFLAGS) $(GMPFLAGS) -DTEST_GMP -DTEST_$(UPPER) tests.c -Iinclude -Irandom -lm -lgmp -o $@

build/minigmp%bench: tests.c build/libwmp.a
	gcc $(CFLAGS) -DTEST_MINIGMP -DTEST_$(UPPER) tests.c -Iinclude -Imini-gmp -Irandom -lm -o $@

BENCHS = toomb sqrtrem millerrabin toomu #add mul div powm toomm


WHY3BENCHFILES = $(addprefix bench/why3, $(BENCHS))
GMPBENCHFILES = $(addprefix bench/gmp, $(BENCHS))
MINIGMPBENCHFILES = $(addprefix bench/minigmp, $(BENCHS))
BENCHFILES = $(WHY3BENCHFILES) $(GMPBENCHFILES) $(MINIGMPBENCHFILES)

$(BENCHFILES): bench/%: build/%bench
	mkdir -p bench
	$< > $@

why3benchs: $(WHY3BENCHFILES)
gmpbenchs: $(GMPBENCHFILES)
minigmpbenchs: $(MINIGMPBENCHFILES)
benchs: why3benchs gmpbenchs minigmpbenchs

plots: $(BENCHFILES)
	make all -C plots

dist: $(EXTRACTED)
	mkdir -p distrib/lib
	touch distrib/ChangeLog
	cp build/*.c build/*.h distrib/lib/
	cd distrib; ./autogen.sh
	cd distrib; make distcheck

tests-dist:
	make -C distrib
	gcc $(CFLAGS) tests.c -DTEST_LIB -Irandom -Idistrib -lgmp -Ldistrib -lwmp -o build/disttests
	./build/disttests
