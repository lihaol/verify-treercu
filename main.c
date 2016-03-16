#include "fake.c"

#define NUM_THREADS 2
#define NUM_INTS    2

//int nr_cpu_ids = NR_CPUS;
int __unbuffered_cnt = 0;
int nondet_int (void);

/*
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
*/


/*
 * Test harness
 */

int x;
int y;

int __unbuffered_cnt;
int __unbuffered_tpr_x;
int __unbuffered_tpr_y;

void rcu_reader(void)
{
	rcu_read_lock();
	__unbuffered_tpr_x = x;
#ifdef FORCE_FAILURE
	rcu_read_unlock();
	cond_resched();
	rcu_read_lock();
#endif
	__unbuffered_tpr_y = y;
	rcu_read_unlock();
}

void *thread_update(void *arg)
{
	fake_acquire_cpu();

	x = 1;
#ifndef FORCE_FAILURE_2
	synchronize_rcu();
#endif
	y = 1;

	fake_release_cpu();
#ifndef RUN
	// Instrumentation for CPROVER
	asm("sync ");
	__unbuffered_cnt++;
#endif
}

void *thread_process_reader(void *arg)
{
	fake_acquire_cpu();

	rcu_reader();

	fake_release_cpu();
#ifndef RUN
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
     
  // Do not consider dyntick-idle mode
  // Use context switch instead
  //rcu_idle_enter();
  rcu_note_context_switch(); 

  if (pthread_create(&tu, NULL, thread_update, NULL))
  	abort();
  if (pthread_create(&tpr, NULL, thread_process_reader, NULL))
  	abort();
  if (pthread_join(tu, NULL))
  	abort();
  if (pthread_join(tpr, NULL))
  	abort();
  assert(__unbuffered_tpr_y == 0 || __unbuffered_tpr_x == 1 ||
         CK_NOASSERT());
  
  return 0;
}

#else

/* Formally verify the test. */
int main(int argc, char *argv[])
{
  // initialisation
  rcu_init();
  rcu_spawn_gp_kthread();
#ifndef CBMC
  //rcu_register_oom_notifier(); // !defined(CONFIG_RCU_FAST_NO_HZ)
  //check_cpu_stall_init(); //!#ifdef CONFIG_RCU_STALL_COMMON 
#endif
  //rcu_verify_early_boot_tests();

  // start to rock
  // timer interrupts
  //__CPROVER_ASYNC_0: timer_interrupt_loop();

  __CPROVER_ASYNC_1: thread_update(0);
  __CPROVER_ASYNC_2: thread_process_reader(0);

  __CPROVER_assume(__unbuffered_cnt == NUM_THREADS);
  assert(__unbuffered_tpr_y == 0 || __unbuffered_tpr_x == 1);

  // grace period has finished
  //assert(ACCESS_ONCE(rcu_sched_state->completed) == 
  //       ACCESS_ONCE(rcu_sched_state->gpnum));

  return 0;
}

#endif
