#!/bin/bash

# run this script as follows:
# ./script/run-rabid.sh <nuser>

NUSER=$1
sh -x ./scripts/run-postal.sh $NUSER
timeout 3m ~/tmp/postal-0.70/rabid -p $NUSER -c 5 -r 10000 [localhost]2110 /tmp/mailtest/users 
