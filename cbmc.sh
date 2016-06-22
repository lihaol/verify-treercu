~/cbmc-releases/5.4/cbmc --ILP32 --unwind 1 --unwindset rcu_spawn_gp_kthread.0:3,rcu_init_levelspread.1:2,rcu_init_one.0:2,rcu_init_one.3:2,rcu_init_one.4:2,rcu_init_one.6:3,rcu_init.3:3 -I . -DCBMC -DPER_CPU_DATA_ARRAY -DFORCE_BUG_1 main.c
# -DFORCE_BUG_1: synchronize_rcu() simply returns immediately
