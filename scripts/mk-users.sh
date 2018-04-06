#!/bin/bash

NUSER=100

rm -rf /tmp/mailtest
ln -s /dev/shm/mailtest /tmp/mailtest

echo "Create $NUSER mailboxes"
for i in `seq 0 $NUSER`;
do
    rm -rf /dev/shm/mailtest/u$i
    mkdir -p /dev/shm/mailtest/u$i/mail
    mkdir -p /dev/shm/mailtest/u$i/tmp
done    

