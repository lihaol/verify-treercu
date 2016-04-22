# need cbmc v5.0
~/cbmc-releases/5.4/cbmc --unwind 3  -I . -DCBMC -DPER_CPU_DATA_ARRAY -DFORCE_FAILURE_2 main.c
# Can add "--mm pso" or "--arch powerpc" for some variety.
# -DFORCE_FAILURE to force failure (bogus dynticks failure)
# -DFORCE_FAILURE_2 to force failure (drop synchronize_rcu())
# -DCBMC_ORDERING_BUG to do unsynchronized accesses to noassert
