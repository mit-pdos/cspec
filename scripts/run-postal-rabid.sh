#!/bin/bash

# run this script as follows: ./script/run-postal-rabid.sh <nuser>
#
# It runs postal first, so if you need both, one can run just this script.

NUSER=$1

echo -n > /tmp/mailtest/users
for i in `seq 1 $NUSER`;
do
    echo "u$i"
    rm -rf /tmp/mailtest/u$i
    mkdir -p /tmp/mailtest/u$i/mail
    mkdir -p /tmp/mailtest/u$i/tmp
    echo "u$i pw" >> /tmp/mailtest/users
done    

./bin/mail-test &
sleep 5
timeout 4m ~/tmp/postal-0.70/postal -p 2525 -t $NUSER -r 10000 localhost /tmp/mailtest/users &
sleep 5
timeout 4m ~/tmp/postal-0.70/rabid -p $NUSER -c 5 -r 10000 [localhost]2110 /tmp/mailtest/users 
kill %1
