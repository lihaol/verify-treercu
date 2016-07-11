 ~/cbmc-releases/5.4/cbmc --ILP32 --unwind 1 --unwindset rcu_spawn_gp_kthread.0:4,rcu_init_levelspread.1:2,rcu_init_one.0:2,rcu_init_one.3:2,rcu_init_one.4:2,rcu_init_one.6:4,rcu_init.3:4 -I . -DCBMC -DPER_CPU_DATA_ARRAY -DFORCE_BUG_7 -DREADER_THREADS_2 main.c

# Use '--mm tso' and '--mm pso' to specify memory model TSO (Intel's x86) and PSO (IBM's Power), respectively; default is SC (Sequential Consistency)
# Use flag -DPROVE_GP to prove a grace period has completed
# Use flags -DFORCE_BUG_* where * is between 1 and 7 inclusive to force different bug-injection scenarios
# Add flag -DREADER_THREADS_2 to use 2 reader threads
