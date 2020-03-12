BENCH ?= no
OVERLAY ?= no
LOCAL ?= $(BENCH)

ifeq ($(LOCAL),yes)
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

.PHONY: all clean extract plots benchs why3benchs gmpbenchs minigmpbenchs

all: extract

clean:
	rm -rf build bench

why3:
	make -C ../..

MLWFILES = \
  mpz_get_str mpz_div2exp mpz_mul2exp mpz_div mpz_mul mpz_sub mpz_add mpz_getset mpz_abs mpz_cmp mpz_cmpabs mpz \
  set_str get_str base_info powm sqrtrem sqrt toom logical div mul sub add compare util

build/extracted: $(addsuffix .mlw, $(MLWFILES))
	mkdir -p build
	rm -f $@
	$(WHY3) extract -D wmpn.drv -D c -L . --recursive --modular --interface -o build/ \
	  --debug c_no_error_msgs wmpn.mlw
	touch $@

build/sqrtinit.h: sqrtinit.ml
	mkdir -p build
	ocaml sqrtinit.ml > build/sqrtinit.h

build/binverttab.h: binverttab.ml
	mkdir -p build
	ocaml binverttab.ml > build/binverttab.h

EXTRACTED = build/extracted build/sqrtinit.h build/binverttab.h

extract: $(EXTRACTED)

CFILES = \
  zutil.c z.c zcmp.c zcmpabs.c zabs.c zadd.c zsub.c zmul.c zdiv.c zmul2exp.c zdiv2exp.c zget_str.c \
  set.c get_str.c set_str.c baseinfo.c powm.c fxp.c sqrt.c sqrt1.c toom.c div.c \
  logical.c logicalold.c logicalutil.c mul_basecase.c sub.c sub_1.c add.c add_1.c \
  compare.c util.c utilold.c int32.c

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

build/gmp%bench: tests.c build/libwmp.a
	gcc $(CFLAGS) $(GMPFLAGS) -DTEST_GMP -DTEST_$(UPPER) tests.c -Iinclude -Irandom -lm -lgmp -o $@

build/minigmp%bench: tests.c build/libwmp.a
	gcc $(CFLAGS) -DTEST_MINIGMP -DTEST_$(UPPER) tests.c -Iinclude -Imini-gmp -Irandom -lm -o $@

BENCHS = toomb sqrtrem millerrabin toomu add mul div powm toomm


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
