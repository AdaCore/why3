all: why3 extract

why3:
	make -C ../../..

extract: why3
	mkdir -p build
	why3 extract -D c -o build/N.c -L . mp2.N

tests: extract check-gmp
	gcc -O2 -Wall -g -std=gnu99 tests.c build/N.c -I$(GMP_DIR) -L$(GMP_LIB) -fomit-frame-pointer -mtune=haswell -march=haswell -fno-tree-vectorize -lgmp -o tests
	gcc -O2 -Wall -g -std=gnu99 -DCOMPARE_MINI tests.c build/N.c -I$(GMP_DIR) -fomit-frame-pointer -mtune=haswell -march=haswell -fno-tree-vectorize -o minitests
	./tests
	./minitests

why3addbench: extract check-gmp
	gcc -O3 -Wall -g -std=gnu99 -DTEST_WHY3 -DTEST_ADD tests.c build/N.c -I$(GMP_DIR) -L$(GMP_LIB) -fomit-frame-pointer -mtune=haswell -march=haswell -fno-tree-vectorize -lgmp -o why3addbench

why3mulbench: extract check-gmp
	gcc -O3 -Wall -g -std=gnu99 -DTEST_WHY3 -DTEST_MUL tests.c build/N.c -I$(GMP_DIR) -L$(GMP_LIB) -fomit-frame-pointer -mtune=haswell -march=haswell -fno-tree-vectorize -lgmp -o why3mulbench

why3divbench: extract check-gmp
	gcc -O3 -Wall -g -std=gnu99 -DTEST_WHY3 -DTEST_DIV tests.c build/N.c -I$(GMP_DIR) -L$(GMP_LIB) -fomit-frame-pointer -mtune=haswell -march=haswell -fno-tree-vectorize -lgmp -o why3divbench

gmpaddbench: extract check-gmp
	gcc -O3 -Wall -g -std=gnu99 -DTEST_GMP -DTEST_ADD tests.c build/N.c -I$(GMP_DIR) -L$(GMP_LIB) -fomit-frame-pointer -mtune=haswell -march=haswell -fno-tree-vectorize -lgmp -o gmpaddbench

gmpmulbench: extract check-gmp
	gcc -O3 -Wall -g -std=gnu99 -DTEST_GMP -DTEST_MUL tests.c build/N.c -I$(GMP_DIR) -L$(GMP_LIB) -fomit-frame-pointer -mtune=haswell -march=haswell -fno-tree-vectorize -lgmp -o gmpmulbench

gmpdivbench: extract check-gmp
	gcc -O3 -Wall -g -std=gnu99 -DTEST_GMP -DTEST_DIV tests.c build/N.c -I$(GMP_DIR) -L$(GMP_LIB) -fomit-frame-pointer -mtune=haswell -march=haswell -fno-tree-vectorize -lgmp -o gmpdivbench

minigmpaddbench: extract
	gcc -O3 -Wall -g -std=gnu99 -DTEST_MINIGMP -DTEST_ADD tests.c build/N.c -I$(GMP_DIR) -fomit-frame-pointer -mtune=haswell -march=haswell -fno-tree-vectorize -o minigmpaddbench

minigmpmulbench: extract
	gcc -O3 -Wall -g -std=gnu99 -DTEST_MINIGMP -DTEST_MUL tests.c build/N.c -I$(GMP_DIR) -fomit-frame-pointer -mtune=haswell -march=haswell -fno-tree-vectorize -o minigmpmulbench

minigmpdivbench: extract
	gcc -O3 -Wall -g -std=gnu99 -DTEST_MINIGMP -DTEST_DIV tests.c build/N.c -I$(GMP_DIR) -fomit-frame-pointer -mtune=haswell -march=haswell -fno-tree-vectorize -o minigmpdivbench

alltests: tests why3addbench why3mulbench why3divbench gmpaddbench gmpmulbench gmpdivbench minigmpaddbench minigmpmulbench minigmpdivbench

data: alltests
	./why3addbench > bench/why3add
	./why3mulbench > bench/why3mul
	./why3divbench > bench/why3div
	./gmpaddbench > bench/gmpadd
	./gmpmulbench > bench/gmpmul
	./gmpdivbench > bench/gmpdiv
	./minigmpaddbench > bench/minigmpadd
	./minigmpmulbench > bench/minigmpmul
	./minigmpdivbench > bench/minigmpdiv

plots: data
	./divplot &
	./divrelative &
	./mulrelative &
	./addrelative &
	./addplot &
	./minidivrelative &
	./minimulrelative &
	./miniaddrelative &
	./gmpdiv &
	./gmpmul &
	./gmpadd &

check-gmp:
ifndef GMP_DIR
	$(error GMP_DIR is undefined)
endif
ifndef GMP_LIB
	$(error GMP_LIB is undefined)
endif
