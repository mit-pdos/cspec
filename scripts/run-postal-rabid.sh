#!/bin/bash

# run this script as follows: ./script/run-postal-rabid.sh <nuser>
#
# It runs postal first, so if you need both, one can run just this script.

NUSER=$1
sh -x ./scripts/run-postal.sh $NUSER &
sleep 20
timeout 4m ~/tmp/postal-0.70/rabid -p $NUSER -c 5 -r 10000 [localhost]2110 /tmp/mailtest/users 
