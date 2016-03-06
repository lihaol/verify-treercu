# need cbmc v5.0
~/cbmc-releases/5.3/cbmc --unwind 5  -I . -DCBMC -DPER_CPU_DATA_ARRAY main.c
# Can add "--mm pso" or "--arch powerpc" for some variety.
# -DFORCE_FAILURE to force failure (bogus dynticks failure)
# -DFORCE_FAILURE_2 to force failure (drop synchronize_rcu(), ineffective!)
# -DCBMC_ORDERING_BUG to do unsynchronized accesses to noassert
