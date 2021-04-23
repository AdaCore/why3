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

.PHONY: clean extract

clean:
	rm -rf build

extract:
	mkdir -p build
	$(WHY3) extract -D cursor.drv -D c -L . --recursive --modular \
		--interface --debug=c_no_error_msgs -o build/ ccursor.PtrCursor

build/tests: build/ptrcursor.c
	gcc -Wall -g -pedantic -Wno-unused-function -std=c11 build/ptrcursor.c -Ibuild -o build/tests
