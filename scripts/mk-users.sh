#!/bin/bash

NUSER=100

echo "Create $NUSER mailboxes"
for i in `seq 0 $NUSER`;
do
    rm -rf /tmp/mailtest/u$i
    mkdir -p /tmp/mailtest/u$i/mail
    mkdir -p /tmp/mailtest/u$i/tmp
done    

