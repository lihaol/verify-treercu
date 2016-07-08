#!/bin/bash

logfile=$1

# Use '--mm tso' and '--mm pso' to specify memory model TSO (Intel's x86) and PSO (IBM's Power), respectively
# Default is SC (Sequential Consistency)
MM=$2

RUNSOLVER=~/runsolver/src/runsolver
EXEC=~/cbmc-releases/5.4/cbmc
CMD="--ILP32 --unwind 1"

# Use LOOP with 1 reader thread and LOOP2 with 2 reader threads
LOOP="--unwindset rcu_spawn_gp_kthread.0:3,rcu_init_levelspread.1:2,rcu_init_one.0:2,rcu_init_one.3:2,rcu_init_one.4:2,rcu_init_one.6:3,rcu_init.3:3 -I ."
LOOP2="--unwindset rcu_spawn_gp_kthread.0:4,rcu_init_levelspread.1:2,rcu_init_one.0:2,rcu_init_one.3:2,rcu_init_one.4:2,rcu_init_one.6:4,rcu_init.3:4 -I ."

# Use flag -DPROVE_GP to prove a grace period has completed
# Use flags -DFORCE_BUG_* where * is between 1 and 7 inclusive to force different bug-injection scenarios
# Add flag -D2_READER_THREADS if using 2 reader threads
FLAGS="-DCBMC -DPER_CPU_DATA_ARRAY -DPROVE_GP"

folder=${logfile}

if [ -d ${folder} ]
then
  echo "Folder " + ${folder} + " already exists."
  exit
fi
 
mkdir ${folder}

${RUNSOLVER} -w ${folder}/${logfile}.watch -v ${folder}/${logfile}.time -o ${folder}/${logfile}.out -d 1 ${EXEC} ${MM} ${CMD} ${LOOP} ${FLAGS} main.c
