EXAMPLESDIR="../../examples"

EX_LIB="-L $EXAMPLESDIR/vacid_0_binary_heaps \
	   -L $EXAMPLESDIR/avl -L $EXAMPLESDIR/ring_decision \
	   -L $EXAMPLESDIR/multiprecision \
	   -L $EXAMPLESDIR/verifythis_2016_matrix_multiplication \
	   -L $EXAMPLESDIR/prover -L $EXAMPLESDIR/double_wp"

BENCHDIR=sessions

EXTRACONF="--extra-config why3extra.conf"

if [ -d $BENCHDIR ]; then
	if [ "$1" = "-r" ]; then
    	    printf "## Removing existing sessions in directory \"$BENCHDIR\"..."
	    rm -rf $BENCHDIR/*
            printf " done\n"
        else
    	    printf "## Keeping existing sessions in directory \"$BENCHDIR\"\n"
	fi
else
    printf "## Creating sessions directory in \"$BENCHDIR\"\n"
    mkdir $BENCHDIR
fi

if [ -z "$(ls -A $BENCHDIR)" ]; then
    printf "## Directory \"$BENCHDIR\" is empty, creating sessions...\n"
    printf "Current time is $(date -u)\n"
    for i in $(cd $EXAMPLESDIR; find . -name "*.mlw"); do
	printf "Creating session for example \"$i\"... \n"
	SESPARENTDIR=$BENCHDIR/$(dirname $i)
        SESDIR=$SESPARENTDIR/$(basename $i .mlw)
	mkdir -p $SESDIR
	../../bin/why3 session create -a split_vc $EX_LIB "$EXAMPLESDIR/$i" -o $SESDIR
	../../bin/why3 session update $EX_LIB $EXTRACONF \
             --add-provers Alt-Ergo,2.5.2,SMT2+BV:Alt-Ergo,2.5.2,SMT2:Alt-Ergo,2.5.2 $SESDIR
    done
    printf "Creation of sessions completed.\n"
    printf "Current time is $(date -u)\n"
else
    printf "## Directory \"$BENCHDIR\" is not empty, jumping directly to bench.\n"
    printf "To restart from empty sessions, run this script with option -r.\n"
fi

SESSIONS=$(find $BENCHDIR -name why3session.xml)

printf "## There are $(echo $SESSIONS | wc -l) session(s) in directory \"$BENCHDIR\". Running why3 bench.\n"
printf "Current time is $(date -u)\n"
for i in $SESSIONS; do
# for i in sessions/avl/avl/why3session.xml; do
	printf "Running bench on session \"$i\"...\n"
	../../bin/why3 bench $i $EX_LIB $EXTRACONF
	printf "Bench on session $i done.\n"
done
printf "Bench completed.\n"
printf "Current time is $(date -u)\n"
