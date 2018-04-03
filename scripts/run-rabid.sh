#!/bin/bash

# run this script as follows: ./script/run-rabid.sh <nuser>
#
# It runs postal first, so if you need both, one can run just this script.

NUSER=$1
./scripts/run-postal.sh $NUSER

sleep 10
./bin/mail-test &
sleep 10
timeout 4m ~/tmp/postal-0.70/rabid -p $NUSER -c 5 -r 10000 [localhost]2110 /tmp/mailtest/users 
kill %1
