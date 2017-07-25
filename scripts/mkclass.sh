#!/bin/sh

#
# create or update POCS-YEAR
#
# if a directory has a file mkclass.ignore, ignore the files listed in that file

umask 2

# update this repository:
CLASSREPO=git@github.com:/mit-pdos/deepspec-pocs

# include only these src/ directories 
SRCS="src/Helpers src/Disk src/Refinement src/NBD \
      src/SepLogic/Mem src/SepLogic/Pred \
      src/Variables src/StatDb \
      src/BadSectorDisk src/RemappedDisk \
      src/TwoDisk src/ReplicatedDisk"

# files/directories to copy
TOPLEVELS="Makefile README.md LICENSE _CoqProject .gitignore scripts/add-preprocess.sh src/POCS.v statdb-cli remap-nbd replicate-nbd lec"

SD=$(cd $(dirname $0)/.. && /bin/pwd)
CD=/tmp/pocs.$$
git clone $CLASSREPO $CD || exit 1

cd $CD && sh -c 'rm -r *'

mkdir -p $CD
mkdir -p $CD/src
mkdir -p $CD/scripts

## Run "make clean" to clear out crud from the extraction directory (like statdb-cli)
( cd $SD && make clean )

for F in $TOPLEVELS; do
  cp -r $SD/$F $CD/$F
  (cd $CD/ && git add $F 2> /dev/null )
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
      (cd $CD/$D && git add $F 2> /dev/null )
    fi
  done)
done

(cd $CD ; git commit -am 'update')

echo "Now, examine and push the repo in $CD"
