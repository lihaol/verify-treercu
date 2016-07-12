#!/bin/bash

MAXRUN="1000"
TIMEOUT="20"
FLAG="-DRUN -DPER_CPU_DATA_ARRAY"

echo ${MAXRUN}' runs for each bug scenario'
echo 'Each run times out in '${TIMEOUT}' seconds'

for i in {1,7}
do
  rm tree 
  cc -I . -g -o tree ${FLAG} -DFORCE_BUG_$i main.c -lpthread

  for j in `seq 1 ${MAXRUN}`
  do
    echo 'BUG_'$i' Run '$j
    timeout ${TIMEOUT} ./runall_helper.sh
  done
done
