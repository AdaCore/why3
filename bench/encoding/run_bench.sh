#!/bin/sh

echo "Run TW + DEC"
why3bench -B benchtwdeco.rc "$@"
echo "Run DIS + DEC"
why3bench -B benchpartialdeco.rc "$@"
echo "Run TW + EXP"
why3bench -B benchtwexp.rc "$@"
echo "Run DIS + EXP"
why3bench -B benchpartialexp.rc "$@"