#!/bin/sh

#
# create or update POCS-YEAR
#
# if a directory has a file mkclass.ignore, ignore the files listed in that file

umask 2

# update this repository:
CLASSREPO=git@github.com:/mit-pdos/deepspec-pocs

# include only these src/ directories 
SRCS="src/Disk src/NBD src/Refinement src/Variables src/StatDb"

# files to copy
TOPLEVELS="Makefile README.md _CoqProject.in .gitignore"

SD=$(cd $(dirname $0)/.. && /bin/pwd)
CD=/tmp/pocs.$$
git clone $CLASSREPO $CD || exit 1

mkdir -p $CD

for F in $TOPLEVELS; do
  cp $SD/$F $CD/$F
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
