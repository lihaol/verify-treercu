#!/bin/bash

i=$1
MAXRUN="1000"
TIMEOUT="60"
FLAG="-DRUN -DPER_CPU_DATA_ARRAY"
BUG=""
EXPT=""

if [ $i -lt -1 ] || [ $i -gt 8 ]
then
  echo 'Input must be between -1 and 8 inclusive'
  exit 
fi

if [ $i == -1 ]
then
  EXPT="PROVE"
elif [ $i == 0 ]
then
  BUG="-DPROVE_GP"
  EXPT="PROVE_GP"
elif [ $i == 8 ]
then
  BUG="-DFORCE_BUG_7 -DREADER_THREADS_2"
  EXPT="BUG_7_2READERS"
else
  BUG="-DFORCE_BUG_"$i
  EXPT="BUG_"$i
fi

EXEC='tree_'${EXPT}

if [ -f ${EXEC} ]
then
  rm ${EXEC}
fi

cc -I . -g -o ${EXEC} ${FLAG} ${BUG} main.c -lpthread

echo 'Start '${MAXRUN}' runs for scenario '${EXPT}
echo 'Each run times out in '${TIMEOUT}'s'
echo ''

for j in `seq 1 ${MAXRUN}`
do
  echo ${EXPT}' run '$j
  timeout ${TIMEOUT} ./run_helper.sh ${EXEC}
  echo ''
done
