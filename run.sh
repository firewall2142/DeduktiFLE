#!/bin/bash
set -e
files=$(dkdep -s --ignore ctslib/*.dk -I ctslib/)

for f in $files; do
bf=$(basename $f)
dune exec -- ./main.exe -I theory/ -I free/ $f > free/$bf
dkcheck -I theory/ -I free/ -e free/$bf
done
