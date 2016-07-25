#!/bin/bash

logfile=$1
CMD=$2

RUNSOLVER=~/runsolver/src/runsolver
EXEC=./run_expt.sh

folder=${logfile}

if [ -d ${folder} ]
then
  echo "Folder " + ${folder} + " already exists."
  exit
fi
 
mkdir ${folder}

${RUNSOLVER} -w ${folder}/${logfile}.watch -v ${folder}/${logfile}.time -o ${folder}/${logfile}.out -d 1 ${EXEC} ${CMD}
