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

clean:
	rm -rf build

dir:
	mkdir -p build

why3:
	make -C ../..

extract: why3 dir
	$(WHY3) extract -D cursor.drv -D c -L . --recursive --modular \
		--interface --debug=c_no_error_msgs -o build/ ccursor.PtrCursor

cfiles: extract
	gcc -Wall -g -pedantic -Wno-unused-function -std=c11 build/ptrcursor.c -Ibuild -o build/tests

tests: cfiles
	./build/tests
