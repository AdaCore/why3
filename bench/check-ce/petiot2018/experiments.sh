#!/usr/bin/env bash
set -Eeuo pipefail

# Replicate the experiments by Petiot (2018) using RAC execution of CEs.

prover="cvc4"
proverce="cvc4-ce"
proverrac="cvc4"
steps=

why3="bin/why3"
outbase="$(dirname $0)"
libdir="$(dirname $0)"
only=""

usage () {
    echo "Usage: $0 [--help] [--prover PROVER] [--ce-prover CE_PROVER] [--stepslimit STEPS] [--rac-prover RAC_PROVER] [--only PROGRAM] [--outdir OUTDIR]"
    (echo "PROVER is used to prove the unmodified programs (default:"
     echo "$prover), CE_PROVER is used to generate counterexamples in the"
     echo "modified programs (default: $proverce). STEPS is used as option"
     echo "--stepslimit for counterexample generation if non-empty (default:"
     echo "$steps). RAC_PROVER is used for option --prover-rac during CE checking"
     echo "(default: $proverrac). If --only PROGRAM is given only the experiments"
     echo "on that program are run. The modified programs and the output is"
     echo "stored in directory OUTDIR.") | fmt
    # The results reported in the F-IDE paper and report were generated with Z3:
    # $ experiments.sh --ce-prover Z3,4.8.4,counterexamples --rac-prover Z3,4.8.4
}

while [ "$#" != 0 ]; do
    case "$1" in
        --prover)
            prover="$2"
            shift 2
            ;;
        --ce-prover)
            proverce="$2"
            shift 2
            ;;
        --stepslimit)
            steps="$2"
            shift 2
            ;;
        --rac-prover)
            proverrac="$2"
            shift 2
            ;;
        --only)
            only="$2"
            shift 2
            ;;
        --outdir)
            outbase="$2"
            shift 2
            ;;
        --help)
            usage
            exit 0
            ;;
        *)
            echo "Unknown option: $1"
            usage
            exit 1
            ;;
    esac
done

really () {
    [ -z "$only" -o "$only" = "$1" ]
}

# Clean experiment output
clean () {
    sed 's/ ([0-9.]\+s, [0-9]\+ steps)\././'
}

# Run why3 prove with CE checking on sub-goal $1 in file $2
why3provece () {
    goal="$1"
    expfile="$2"
    command=("$why3" prove
             --library="$libdir" "$expfile"
             --apply-transform=split_vc
             --prover="$proverce"
             --timelimit=15
             --check-ce --rac-prover="$proverrac"
             --sub-goal="$goal")
    [ -n "$steps" ] && command+=(--stepslimit="$steps")
    echo "${command[@]}" 2>&1
    "${command[@]}" 2>&1 || [ $? -eq 2 ]
}

# Run an experiment with name $1. The program modifications are read from stdin.
# Stdout and stderr of the calls to why3 goes to stdout and will be piped to
# outfiles in under $outbase/, progress goes to stderr.
experiment () {
    experiment=$1
    echo -n "Experiment $experiment:" >&2
    echo "* Experiment $experiment"
    echo "** Original"
    prove_opts=(--apply-transform=split_vc --prover="$prover" --library="$libdir")
    $why3 prove "${prove_opts[@]}" "$libdir/$experiment.mlw"
    mkdir -p "$outbase/experiments"
    while IFS=$'\t' read -r id lines mod goal; do
        echo -n " $id" >&2
        name="$experiment-$id"
        expfile="$outbase/experiments/$name.mlw"
        echo "** $name"
        sedargs=()
        for line in $lines; do
            sedargs+=(-e "$line c $mod")
        done
        sed "${sedargs[@]}" "$libdir/$experiment.mlw" > "$expfile"
        why3provece "$goal" "$expfile"
    done
    echo >&2
}

# Input is TSV with columns: ID, Line(s), Line replacement, Goal

really isqrt && ( experiment isqrt | clean > "$outbase/isqrt.out" ) <<EOF
S1	4	(* empty *)	:10@loop invariant init
S2	8	let z = int_ref (2 * n + 1) in	:13@loop invariant init
S3	13	invariant I4 { !z = 2 * !r + 1 }	:13@loop invariant init
S4	15	y := !y - !z;	:11@loop invariant preservation
S5	13	(* empty *)	:11@loop invariant preservation
S6	9	while !y > n + 1 do	:5@postcondition
S7	12	(* empty *)	:5@postcondition
S8	19	!r - 1	:5@postcondition
S9	14	variant { !r - n }	:14@loop variant decrease
S10	10	invariant I1 { !r <= n }	:14@loop variant decrease
EOF

really binary_search && (  experiment binary_search | clean > "$outbase/binary_search.out" ) <<EOF
B1	15	variant { t.length - !r }	:15@loop variant decrease
B2	16	let m = div (!l + !r) 2 in	:15@loop variant decrease
B3	5	(* empty *)	:14@loop invariant preservation
B4	13 14	(* empty *)	:8@postcondition
EOF

really rgf && (  experiment rgf | clean > "$outbase/rgf.out"  ) <<EOF
R1	26	(* empty *)	:41@precondition
R4	40	a[!i] <- a[!i] + 2;	:41@precondition
EOF

git diff --exit-code "*.out"
