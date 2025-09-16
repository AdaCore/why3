# Helper script to upgrade sessions from one prover to another.
# WARNING: This script is experimental and not very well tested.
#
# The script attempts to upgrade the proofs from the old prover to the new
# prover. If the upgrade fails, it will keep the node as proved by the old
# prover, and it will store the generated files for which the old prover succeeds
# and the new prover fails.
# Some assumptions made by the script:
# - Two configuration files need to be present in misc/:
#   - why3.conf.<old_version> with a working configuration for the old version of the prover
#   - why3.conf.<new_version> with a working configuration for the new version and an upgrade-prover section for the old version
# - The file is completely proved (proof attempts for all unproved nodes will be added)
# 

# These are useful in the event the extension of the generated files is different
New_extension=psmt2
Old_extension=psmt2

DEBUG=0
GLOBAL_OUT=./misc/upgrade_sessions_out
SESSIONS_DIR=./examples/

# Read prover, new, old from command line
while getopts "p:n:o:Dg:" opt; do
  case $opt in
    p) Prover=$OPTARG ;;
    n) New=$OPTARG ;;
    o) Old=$OPTARG ;;
    D) DEBUG=1 ;;
    g) GLOBAL_OUT=$OPTARG ;;
    \?) echo "Invalid option: -$OPTARG" ;;
  esac
done

function usage() {
  echo "Usage: upgrade_sessions.sh -p <prover> -n <new_version> -o <old_version> [-D] [-g <output_dir>]"
  echo "  -p prover: prover to upgrade"
  echo "  -n new: new version of the prover"
  echo "  -o old: old version of the prover"
  echo "  -D: enable debug mode"
  echo "  -g global_out: output directory for generated files"
  echo "The script expects the following files to be in the same directory as the script:"
  echo "- why3.conf.<old_version>, containing a working configuration for the old version of the prover"
  echo "- why3.conf.<new_version>, containing a working configuration for the new version and an upgrade-prover section for the old version"
  exit 1
}

if [ -z "$Prover" ] || [ -z "$New" ] || [ -z "$Old" ]; then
  usage
  exit 1
fi

if [ ! -f "./misc/why3.conf.$Old" ] || [ ! -f "./misc/why3.conf.$New" ]; then
  echo "Error: why3.conf.$Old and why3.conf.$New must be in the same directory as the script."
  exit 1
fi

WHY3_OLD="why3 --config=./misc/why3.conf.$Old"
WHY3_NEW="why3 --config=./misc/why3.conf.$New"

function lib_param() {
  # Add -L parameter to why3 if the session is in some subdirectory
  if [ "$(dirname $1)" != $SESSIONS_DIR ]; then
    echo "-L $(dirname $1)"
  fi
}

function cp_with_suffix() {
  INFILE=$1
  OUTDIR=$2
  OUTNAME=$3
  SUFFIX=$4
  OUTFILE="$OUTNAME$SUFFIX"
  if [ -f "$OUTDIR/$OUTFILE" ]; then
    i=1
    while [ -f "$OUTDIR/$OUTNAME-$i$SUFFIX" ]; do
      i=$((i+1))
    done
    OUTFILE="$OUTNAME-$i$SUFFIX"
  fi
  cp "$INFILE" "$OUTDIR/$OUTFILE"
}

function first_pass() {
  echo "Marking old prover as obsolete..."
  $WHY3_OLD session update --filter-prover $Prover,$Old --mark-obsolete $1
  echo "Forcing upgrade..."
  OUTDIR=$GLOBAL_OUT/${1#$SESSIONS_DIR}
  mkdir -p $OUTDIR
  # Replay is forced: the idea is to upgrade the prover, and leave new failures as unproved.
  # If the forced upgrade succeeds, then nothing else is needed and we exit with a special code
  $WHY3_NEW replay $(lib_param $1) $1 -P $Prover,$Old --force >$OUTDIR/upgrade.log 2>&1
  if [ $? -eq 0 ]; then
    echo "Upgrade succeded, no need for futher processing"
    return 2
  fi
  echo "Getting generated prover files of nodes failing with new prover..."
  OUTPUTS=$($WHY3_NEW replay $(lib_param $1) $1 -P $Prover,$New --debug call_prover 2>&1 | grep "File.*Timeout")
  if [ $DEBUG -eq 1 ]; then
    echo "DEBUG: New SMT2 files"
    echo "$OUTPUTS"
  fi
  echo "Copying files..."
  while IFS= read -r line; do
    INFILE=$(echo "$line" | sed 's/.*File "\(.*\)", line.*/\1/')
    OUTNAME=$(basename "$INFILE" .$New_extension)
    OUTNAME=${OUTNAME:11}
    cp_with_suffix "$INFILE" $OUTDIR "$OUTNAME" _$New.$New_extension
  done <<< "$OUTPUTS"
}

function second_pass() {
  echo "Adding old prover to all unproved nodes..."
  $WHY3_OLD session update --filter-proved=no --filter-is-leaf=yes --add-provers=$Prover,$Old $1
  echo "Removing failed proof attempts with new prover..."
  $WHY3_NEW session update --filter-prover $Prover,$New --filter-status=timeout --remove-proofs $1
  echo "Forcing replay on all nodes with old prover..."
  $WHY3_OLD replay $(lib_param $1) $1 -P $Prover,$Old --force >/dev/null 2>&1
  echo "Getting generated prover files successfully proved by old prover..."
  # At this stage, nodes that are still on old version are those where the new prover failed
  OUTPUTS=$($WHY3_OLD replay $(lib_param $1) $1 -P $Prover,$Old --debug call_prover 2>&1 | grep File)
  if [ $DEBUG -eq 1 ]; then
    echo "DEBUG: Old SMTv2 files"
    echo "$OUTPUTS"
  fi
  echo "Copying files..."
  OUTDIR=$GLOBAL_OUT/${1#$SESSIONS_DIR}
  mkdir -p $OUTDIR
  while IFS= read -r line; do
    INFILE=$(echo "$line" | sed 's/.*File "\(.*\)", line.*/\1/')
    OUTNAME=$(basename "$INFILE" .$Old_extension)
    OUTNAME=${OUTNAME:11}
    cp_with_suffix "$INFILE" $OUTDIR "$OUTNAME" _$Old.$Old_extension
  done <<< "$OUTPUTS"
}

function upgrade_sessions() {
  first_pass $1
  if [ $? -eq 2 ]; then
    return 0
  else
    second_pass $1
  fi
}

function main_loop() {
  for i in $(find $1 -name "*.xml" -exec grep -l "version=\"$Old" {} \;);
  do
    # Ignore folders: tests-provers, logic
    if [[ $i == *"tests-provers"* ]] || [[ $i == *"logic"* ]]; then
      continue
    fi
    echo "Running on session $i"
    COMMAND="$WHY3_NEW replay -P $Prover,$Old $(dirname $i) $(lib_param $(dirname $i))"
    if [ $DEBUG -eq 1 ]; then
      echo "DEBUG: Running command: $COMMAND"
      $COMMAND
    else
      $COMMAND >/dev/null 2>&1
    fi
    if [ $? -eq 0 ]; then
      echo "Upgrade successful, going to next session"
      continue
    else
      echo "Upgrade failed, processing session"
      upgrade_sessions $(dirname $i)
    fi
  done
}

main_loop $SESSIONS_DIR