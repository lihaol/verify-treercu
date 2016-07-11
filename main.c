#include "fake.c"

#define NUM_THREADS 2
//#define NUM_INTS 2

#if 0
int nondet_int(void);

void timer_interrupt(int cpu)
{
  // schedule work to different CPUs
__CPROVER_atomic_begin();
  for (int i=0; i<NUM_THREADS; i++) {
    int c = nondet_int();
    __CPROVER_assume(c >= 0 && c < NUM_THREADS);
    which_cpu[i] = c;
  }
__CPROVER_atomic_end();

  rcu_check_callbacks(cpu);
}

void timer_interrupt_loop() {
  for (int i=0; i<NUM_INTS; i++) {
    int c = nondet_int();
    __CPROVER_assume(c >= 0 && c < NUM_THREADS);
    timer_interrupt(c);
    //rcu_check_callbacks(NULL);
  }
}
#endif


/*
 * Test harness
 */
int x;
int y;

int __unbuffered_cnt;
int __unbuffered_tpr_x;
int __unbuffered_tpr_y;

#ifdef RUN
struct thread_info {
	unsigned long my_cpu_id;
};
#endif

void rcu_reader(void)
{
	rcu_read_lock();
	__unbuffered_tpr_x = x;
	__unbuffered_tpr_y = y;
	rcu_read_unlock();
}

void *thread_update(void *arg)
{
#ifdef CBMC
        my_smp_processor_id = *((unsigned int*)arg);
#else
	struct thread_info *tinfo = arg;
	my_smp_processor_id = tinfo->my_cpu_id;
#endif

	fake_acquire_cpu();

	x = 1;
	synchronize_rcu();
	y = 1;

	fake_release_cpu();
#ifdef CBMC
	// Instrumentation for CPROVER
	asm("sync ");
	__unbuffered_cnt++;
#endif
}

void *thread_process_reader(void *arg)
{
#ifdef CBMC
        my_smp_processor_id = *((unsigned int*)arg);
#else
	struct thread_info *tinfo = arg;
	my_smp_processor_id = tinfo->my_cpu_id;
#endif

	fake_acquire_cpu();

	rcu_reader();

	fake_release_cpu();
	rcu_process_callbacks(NULL);

#ifdef CBMC
	// Instrumentation for CPROVER
	asm("sync ");
	__unbuffered_cnt++;
#endif
}

#ifdef RUN

/* Actually run the test. */
int main(int argc, char *argv[])
{
	pthread_t tu;
	pthread_t tpr;
	struct thread_info tinfo_tu = {(0)};
	struct thread_info tinfo_tpr = {(1)};
#ifdef READER_THREADS_2
	struct thread_info tinfo_tpr2 = {(2)};
	pthread_t tpr2;
#endif

	// initialisation
	rcu_init();
	rcu_spawn_gp_kthread();
	//rcu_register_oom_notifier(); // !defined(CONFIG_RCU_FAST_NO_HZ)
	//check_cpu_stall_init(); //!#ifdef CONFIG_RCU_STALL_COMMON 
	//rcu_verify_early_boot_tests();

	// sanity check
#ifdef READER_THREADS_2
        WARN_ON(NR_CPUS != 3);
#else
        WARN_ON(NR_CPUS != 2);
#endif
        WARN_ON(RCU_FANOUT_LEAF != 16);
        WARN_ON(RCU_NUM_LVLS != 1);
        WARN_ON(NUM_RCU_NODES != 1);

	int i;
	for (i=0; i<NR_CPUS; i++) {
		pthread_mutex_init(&cpu_lock[i], NULL);
		//pthread_mutex_init(&irq_lock[i], NULL);
	}

	// Do not consider dyntick-idle mode
	// Use context switch instead
	//rcu_idle_enter();
	rcu_note_context_switch(); 
	
	if (pthread_create(&tu, NULL, thread_update, &tinfo_tu))
		abort();
	if (pthread_create(&tpr, NULL, thread_process_reader, &tinfo_tpr))
		abort();
#ifdef READER_THREADS_2
	if (pthread_create(&tpr2, NULL, thread_process_reader, &tinfo_tpr2))
		abort();
#endif
	if (pthread_join(tu, NULL))
		abort();
	if (pthread_join(tpr, NULL))
		abort();
#ifdef READER_THREADS_2
	if (pthread_join(tpr2, NULL))
		abort();
#endif

#if defined(PROVE_GP)    || defined(FORCE_BUG_2) || defined(FORCE_BUG_3) || \
    defined(FORCE_BUG_4) || defined(FORCE_BUG_5) || defined(FORCE_BUG_6)
	assert(0);
#else
	assert(__unbuffered_tpr_y == 0 || __unbuffered_tpr_x == 1);
	       //|| CK_NOASSERT());
#endif
	
	return 0;
}

#else

/* Formally verify the test. */
int main(int argc, char *argv[])
{
	// initialisation
	rcu_init();
	rcu_spawn_gp_kthread();
	//rcu_register_oom_notifier(); // !defined(CONFIG_RCU_FAST_NO_HZ)
	//check_cpu_stall_init(); //!#ifdef CONFIG_RCU_STALL_COMMON 
	//rcu_verify_early_boot_tests();
	
	// sanity check
#ifdef READER_THREADS_2
        WARN_ON(NR_CPUS != 3);
#else
        WARN_ON(NR_CPUS != 2);
#endif
        WARN_ON(RCU_FANOUT_LEAF != 16);
        WARN_ON(RCU_NUM_LVLS != 1);
        WARN_ON(NUM_RCU_NODES != 1);

	// start to rock
	// timer interrupts
	//__CPROVER_ASYNC_0: timer_interrupt_loop();
	
        unsigned int my_cpu_id0 = 0;
        unsigned int my_cpu_id1 = 1;
#ifdef READER_THREADS_2
        unsigned int my_cpu_id2 = 2;
#endif
	__CPROVER_ASYNC_0: thread_update(&my_cpu_id0);
	__CPROVER_ASYNC_1: thread_process_reader(&my_cpu_id1);
#ifdef READER_THREADS_2
	__CPROVER_ASYNC_2: thread_process_reader(&my_cpu_id2);
#endif
	
	__CPROVER_assume(__unbuffered_cnt == NUM_THREADS);
#if defined(PROVE_GP)    || defined(FORCE_BUG_2) || defined(FORCE_BUG_3) || \
    defined(FORCE_BUG_4) || defined(FORCE_BUG_5) || defined(FORCE_BUG_6)
	assert(0);
#else
	assert(__unbuffered_tpr_y == 0 || __unbuffered_tpr_x == 1);
#endif
	
	// grace period has finished
	//assert(ACCESS_ONCE(rcu_sched_state->completed) == 
	//       ACCESS_ONCE(rcu_sched_state->gpnum));
	
	return 0;
}

#endif
