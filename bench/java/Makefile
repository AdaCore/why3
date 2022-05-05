
all:
	why3 prove test.mlw
	rm -f *java
	for m in A C; do \
	why3 --debug java_extraction extract -D java -L . --modular -o . test.$$m; done
