#!/bin/bash

set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
cd "$DIR/.."
NPROC=$1
NMSG=100000
N=$((NMSG * NPROC))
TIMEFORMAT='real %R nuser %U sys %S (s)'
echo "== gomail $NPROC $NMSG $N $(date) == "
for i in $(seq 1 "$NPROC")
do
    echo "== gomail $i $((N / i))"
    ./scripts/mk-users.sh; time ( cd ./gomail/msrv && GOMAIL_NPROC=$i GOMAIL_NITER=$((N / i)) go test -v )
    sleep 1
done    

