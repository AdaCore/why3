# useful script for git bisect

(make clean && autoconf && ./configure --enable-local --disable-coq-libs --disable-isabelle-libs > /dev/null && make -j) || exit 125
bin/why3 config detect > /dev/null
/bin/time -f "%e" bin/why3 prove examples/bts/951.mlw >/dev/null 2>time.log
t=$(cat time.log)
echo $t
case $t in
    0*) exit 0
        ;;
    [1-9]*) exit 1
        ;;
    *) exit 125
esac
