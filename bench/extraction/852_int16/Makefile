
BENCH ?= no

ifeq ($(BENCH),yes)
  WHY3=../../../bin/why3.opt
else
  ifeq ($(BINDIR),)
    WHY3=why3
  else
    WHY3=$(BINDIR)/why3
  endif
endif

.PHONY: clean extract

clean:
	rm -rf build

extract build/852_int16.c:
	mkdir -p build
	$(WHY3) extract -D c -o build/852_int16.c 852_int16.mlw

build/tests: build/852_int16.c
	gcc -Wall -g -pedantic -Wno-unused-function -std=c11 build/852_int16.c main.c -o build/tests
