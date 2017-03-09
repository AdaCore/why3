all: why3 extract
why3:
	make -C ../../..
extract:
	why3 extract -D c -o build mp2.mlw -T N
tests: extract check-gmp
	gcc -O3 -Wall -g -std=gnu99 tests.c build/mp2.mlw__N.c -I$(GMP_DIR) -lgmp -o tests
benchwhy3: extract check-gmp
	gcc -O3 -Wall -g -std=gnu99 -DTEST_WHY3 tests.c build/mp2.mlw__N.c -I$(GMP_DIR) -lgmp -o why3bench
benchgmp: extract check-gmp
	gcc -O3 -Wall -g -std=gnu99 -DTEST_GMP tests.c build/mp2.mlw__N.c -I$(GMP_DIR) -lgmp -o gmpbench
alltests: tests benchwhy3 benchgmp
check-gmp:
ifndef GMP_DIR
	$(error GMP_DIR is undefined)
endif

