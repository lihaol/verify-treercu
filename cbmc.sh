# need cbmc v5.0
~/cbmc-releases/5.4/cbmc --ILP32 --unwind 1 --unwindset rcu_init_levelspread.1:2,rcu_init_one.0:2,rcu_init_one.3:2,rcu_init_one.4:2,rcu_init_one.6:3,rcu_init.3:3 -I . -DCBMC -DPER_CPU_DATA_ARRAY -DFORCE_FAILURE_2 main.c
# Can add "--mm pso" or "--arch powerpc" for some variety.
# -DFORCE_FAILURE to force failure (bogus dynticks failure)
# -DFORCE_FAILURE_2 to force failure (drop synchronize_rcu())
# -DCBMC_ORDERING_BUG to do unsynchronized accesses to noassert
# --ILP32 to use 32bit address
