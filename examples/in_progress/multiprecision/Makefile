all: why3 extract

why3:
	make -C ../../..

extract: why3
	mkdir -p build
	why3 extract -D c -o build/N.c -L . mp2.N

tests: extract check-gmp
	gcc -O2 -Wall -g -std=gnu99 tests.c build/N.c -I$(GMP_DIR) -L$(GMP_LIB) -fomit-frame-pointer -mtune=haswell -march=haswell -fno-tree-vectorize -lgmp -o build/tests
	gcc -O2 -Wall -g -std=gnu99 -DCOMPARE_MINI tests.c build/N.c -I$(GMP_DIR) -fomit-frame-pointer -mtune=haswell -march=haswell -fno-tree-vectorize -o build/minitests
	./build/tests
	./build/minitests

build/why3%bench: extract check-gmp
	gcc -O3 -Wall -g -std=gnu99 -DTEST_WHY3 -DTEST_`echo $* | tr [:lower:] [:upper:]` tests.c build/N.c -I$(GMP_DIR) -L$(GMP_LIB) -fomit-frame-pointer -mtune=haswell -march=haswell -fno-tree-vectorize -lgmp -o $@

build/gmp%bench: extract check-gmp
	gcc -O3 -Wall -g -std=gnu99 -DTEST_GMP -DTEST_`echo $* | tr [:lower:] [:upper:]` tests.c build/N.c -I$(GMP_DIR) -L$(GMP_LIB) -fomit-frame-pointer -mtune=haswell -march=haswell -fno-tree-vectorize -lgmp -o $@

build/minigmp%bench: extract
	gcc -O3 -Wall -g -std=gnu99 -DTEST_MINIGMP -DTEST_`echo $* | tr [:lower:] [:upper:]` tests.c build/N.c -I$(GMP_DIR) -fomit-frame-pointer -mtune=haswell -march=haswell -fno-tree-vectorize -o $@

alltests: tests build/why3addbench build/why3mulbench build/why3divbench build/gmpaddbench build/gmpmulbench build/gmpdivbench build/minigmpaddbench build/minigmpmulbench build/minigmpdivbench

data: alltests
	mkdir -p bench
	./build/why3addbench > bench/why3add
	./build/why3mulbench > bench/why3mul
	./build/why3divbench > bench/why3div
	./build/gmpaddbench > bench/gmpadd
	./build/gmpmulbench > bench/gmpmul
	./build/gmpdivbench > bench/gmpdiv
	./build/minigmpaddbench > bench/minigmpadd
	./build/minigmpmulbench > bench/minigmpmul
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
