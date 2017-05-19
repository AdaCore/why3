all: why3 extract
why3:
	make -C ../../..
extract: why3
	why3 extract -D c -D mp.drv -o build/N.c -L . mp2.N
tests: extract check-gmp
	gcc -O3 -Wall -g -std=gnu99 tests.c build/N.c -I$(GMP_DIR) -L$(GMP_LIB) -lgmp -o tests
	./tests
why3addbench: extract check-gmp
	gcc -O3 -Wall -g -std=gnu99 -DTEST_WHY3 -DTEST_ADD tests.c build/N.c -I$(GMP_DIR) -L$(GMP_LIB) -lgmp -o why3addbench
why3mulbench: extract check-gmp
	gcc -O3 -Wall -g -std=gnu99 -DTEST_WHY3 -DTEST_MUL tests.c build/N.c -I$(GMP_DIR) -L$(GMP_LIB) -lgmp -o why3mulbench
why3divbench: extract check-gmp
	gcc -O3 -Wall -g -std=gnu99 -DTEST_WHY3 -DTEST_DIV tests.c build/N.c -I$(GMP_DIR) -L$(GMP_LIB) -lgmp -o why3divbench
gmpaddbench: extract check-gmp
	gcc -O3 -Wall -g -std=gnu99 -DTEST_GMP -DTEST_ADD tests.c build/N.c -I$(GMP_DIR) -L$(GMP_LIB) -lgmp -o gmpaddbench
gmpmulbench: extract check-gmp
	gcc -O3 -Wall -g -std=gnu99 -DTEST_GMP -DTEST_MUL tests.c build/N.c -I$(GMP_DIR) -L$(GMP_LIB) -lgmp -o gmpmulbench
gmpdivbench: extract check-gmp
	gcc -O3 -Wall -g -std=gnu99 -DTEST_GMP -DTEST_DIV tests.c build/N.c -I$(GMP_DIR) -L$(GMP_LIB) -lgmp -o gmpdivbench

alltests: tests why3addbench why3mulbench why3divbench gmpaddbench gmpmulbench gmpdivbench

data: alltests
	./why3addbench > bench/why3add
	./why3mulbench > bench/why3mul
	./why3divbench > bench/why3div
	./gmpaddbench > bench/gmpadd
	./gmpmulbench > bench/gmpmul
	./gmpdivbench > bench/gmpdiv

plots: data
	./divplot &
	./divrelative &
	./mulrelative &
	./addrelative &

check-gmp:
ifndef GMP_DIR
	$(error GMP_DIR is undefined)
endif
ifndef GMP_LIB
	$(error GMP_LIB is undefined)
endif
