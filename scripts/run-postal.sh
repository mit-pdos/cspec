#!/bin/bash

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

echo "run-postal $NUSER"

./bin/mail-test &
sleep 5
timeout 4m ~/tmp/postal-0.70/postal -p 2525 -t $NUSER -r 10000 localhost /tmp/mailtest/users
kill %1
