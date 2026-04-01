#!/bin/bash

cmd="$HOME/tmp/smt-solvers/cvc5"
dir="resources/sygus_sel"
outfile="cvc_bench.txt"
complfile="cvc_completed.txt"
success=0
if [[ -n "$1" ]]; then
    outfile=$1
fi

:> $complfile
all=$(find $dir -name '*.sl' | wc -l)
function run() {
    i=0
    t=$(mktemp -d)
    for f in $(find $dir -name '*.sl')
    do
        echo
        echo ==========
        echo "[$i/$success/$all] $f:"
        timeout 300s time -p $cmd $f
        rc=$?
        if [[ $rc -eq 0 ]]; then
            success=$((success+1))
            echo "$f" >> $complfile
        fi
        i=$(($i+1))
    done

    echo
    echo "Completed $success/$all"
}

run 2>&1 | tee $outfile
