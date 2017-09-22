#!/bin/sh

#
# create or update POCS-YEAR
#
# if a directory has a file mkclass.ignore, ignore the files listed in that file

umask 2

# update this repository:
CLASSREPO=git@github.com:mit-pdos/6.826-2017-labs

# include only these src/ directories 
SRCS="src/Helpers src/Spec src/Lab1"

# files/directories to copy
TOPLEVELS="README.md LICENSE _CoqProject .gitignore scripts/add-preprocess.sh src/POCS.v statdb-cli"

# current Makefile
MAKEFILE_NAME=Makefile.lab1

SD=$(cd $(dirname $0)/.. && /bin/pwd)
CD=/tmp/pocs.$$
git clone $CLASSREPO $CD || exit 1

cd $CD && sh -c 'rm -r *'

mkdir -p $CD
mkdir -p $CD/src
mkdir -p $CD/scripts

## Run "make clean" to clear out crud from the extraction directory (like statdb-cli)
( cd $SD && make clean )

cp $SD/$MAKEFILE_NAME $CD/Makefile

for F in $TOPLEVELS; do
  cp -r $SD/$F $CD/$F
done

for D in `echo $SRCS`
do
  mkdir -p $CD/$D || exit 1
  (cd $SD/$D
  for F in `ls`
  do
    echo $F
    if [ -s mkclass.ignore ]
    then
      if grep -q $F mkclass.ignore
      then
        I=1
      else
        I=0
      fi
    else
      I=0
    fi
    if [ "$F" = "out" ]
    then
      I=1
    fi
    if [ "$F" = "mkclass.ignore" ]
    then
      I=1
    fi
    if echo $F | grep -q '#$'
    then
      I=1
    fi
    if [ $I -eq 1 ]
    then
      echo "ignore $F"
    else
      $SD/scripts/mklab.pl $CD/$D $F
    fi
  done)
done

(cd $CD && git add .)

(cd $CD ; git commit -am 'update')

echo "Now, examine and push the repo in $CD"
