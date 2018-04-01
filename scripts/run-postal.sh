#!/bin/bash

NUSER=$1

echo -n > /tmp/mailtest/users
for i in `seq 1 $NUSER`;
do
    echo u$i
    rm -rf /tmp/mailtest/u$i
    mkdir -p /tmp/mailtest/u$i/mail
    mkdir -p /tmp/mailtest/u$i/tmp
    echo "u$i" >> /tmp/mailtest/users
done    

postal -p 2525 -t $NUSER -r 10000 localhost /tmp/mailtest/users

# mail-test: <socket: 26>: hGetLine: end of file

