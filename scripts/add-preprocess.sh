#!/bin/bash
set -e

# cross-platform sed (because OS X only has BSD sed):
# see http://stackoverflow.com/questions/5694228/sed-in-place-flag-that-works-both-on-mac-bsd-and-linux

sed -i.bak $'1s|^|{-# OPTIONS_GHC -F -pgmF ./fiximports.py #-}\\\n|' "$1"
rm "$1.bak"
