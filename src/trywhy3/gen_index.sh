#!/bin/sh


for i in $*
do
    EXT=""
    case "$i" in
	*.mlw)
	    EXT=".mlw"
	    ;;
	*.why)
	    EXT=".why"
	    ;;
	*)
	    echo "Warning: unknown extension for file $i";
	    continue
	    ;;
    esac
    B=$(basename "$i" "$EXT" | tr _ ' ' |  sed -e 's/\b\(.\)/\u\1/g');
    echo "$B"
    echo "$i"
done
