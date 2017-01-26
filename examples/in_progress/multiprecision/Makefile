all: why3 extract
why3:
	make -C ../../..
extract:
	why3 extract -D c -o build mp2.mlw -T N
tests: extract
	gcc -O3 -Wall -g -std=gnu99 tests.c build/mp2.mlw__N.c -lgmp -o tests
benchwhy3: extract
	gcc -O3 -Wall -g -std=gnu99 -DTEST_WHY3 tests.c build/mp2.mlw__N.c -lgmp -o why3bench
benchgmp: extract
	gcc -O3 -Wall -g -std=gnu99 -DTEST_GMP tests.c build/mp2.mlw__N.c -lgmp -o gmpbench
alltests: tests benchwhy3 benchgmp
