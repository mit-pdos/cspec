#!/bin/bash

sed -i '' $'1s|^|{-# OPTIONS_GHC -F -pgmF ./fiximports.py #-}\\\n|' "$1"
