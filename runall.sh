#!/bin/bash

MAXRUN="100"
TIMEOUT="20"
FLAG="-DRUN -DPER_CPU_DATA_ARRAY"
BUG=""
EXPT=""

echo '* '${MAXRUN}' runs for each scenario'
echo '* Each run times out in '${TIMEOUT}' seconds'
echo ''

for i in {-1..8}
do
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
    EXPT="BUG_7_2"
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

  echo '=================================='
  echo ''
  echo 'Start '${MAXRUN}' runs for scenario '${EXPT}':'
  echo ''

  for j in `seq 1 ${MAXRUN}`
  do
    echo ${EXPT}' run '$j
    timeout ${TIMEOUT} ./run_helper.sh ${EXEC}
    echo ''
  done
done
