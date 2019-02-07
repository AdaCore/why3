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

why3:
	make -C ../..

extract: why3
	$(WHY3) extract -D cursor.drv -D c -L . -o ptrcursor.c ccursor.PtrCursor

main: extract
	gcc -Wall -g -pedantic -Wno-unused-function -c -std=c11 ptrcursor.c
