#!/bin/bash

set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
cd "$DIR/.."
NPROC=$1
NMSG=100000
N=$((NMSG * NPROC))
TIMEFORMAT='real %R nuser %U sys %S (s)'
echo "== mail-test $NPROC $NMSG $N $(date) == "
for i in $(seq 1 "$NPROC")
do
    echo "== mail-test $i $((N / i))"
    ./scripts/mk-users.sh; time ./bin/mail-test "$i" "$((N / i))" 1 1
    sleep 1
done    

