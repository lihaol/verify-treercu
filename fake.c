/*
 * "Fake" definitions to scaffold a Linux-kernel UP environment.
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, you can access it online at
 * http://www.gnu.org/licenses/gpl-2.0.html.
 *
 * Copyright IBM Corporation, 2015
 *
 * Authors: Paul E. McKenney <paulmck@linux.vnet.ibm.com>
 *          Lihao Liang <lihao.liang@cs.ox.ac.uk>
 */

#include "fake.h"
#include "fake_sat.h"
#include "fake_tree.h"

int nr_cpu_ids = NR_CPUS;

/* Just say "no" to memory allocation. */
void kfree(const void *p)
{
}

/* Model callback wakeme_after_rcu() */
int wait_rcu_gp_flag;
void wait_rcu_gp(call_rcu_func_t crf)
{
  wait_rcu_gp_flag = 1;
  __CPROVER_assume(wait_rcu_gp_flag == 0);
}

/*
 * Definitions to emulate CPU, interrupts, and scheduling.
 *
 * There is a cpu_lock, when held, the corresponding thread is running.
 * An irq_lock indicates that the corresponding thread has interrupts
 *	masked, perhaps due to being in an interrupt handler.  Acquire
 *	cpu_lock first, then irq_lock.  You cannot disable interrupts
 *	unless you are running, after all!
 * An nmi_lock indicates that the corresponding thread is in an NMI
 *	handler.  You cannot acquire either cpu_lock or irq_lock while
 *	holding nmi_lock.
 */

#ifdef CBMC
int cpu_lock[NR_CPUS];
int irq_lock[NR_CPUS];
int nmi_lock[NR_CPUS];
#else
pthread_mutex_t cpu_lock = PTHREAD_MUTEX_INITIALIZER;
pthread_mutex_t irq_lock = PTHREAD_MUTEX_INITIALIZER;
pthread_mutex_t nmi_lock = PTHREAD_MUTEX_INITIALIZER;
#endif

void rcu_idle_enter(void);
void rcu_idle_exit(void);
static void rcu_process_callbacks(struct softirq_action *unused);
static int rcu_gp_in_progress(struct rcu_state *rsp);
int rcu_jiffies_till_stall_check(void);

void fake_acquire_cpu(void)
{
#ifdef CBMC
	if (__sync_fetch_and_add(&cpu_lock[smp_processor_id()], 1))
		SET_NOASSERT();
#else
	if (pthread_mutex_lock(&cpu_lock))
		exit(-1);
#endif
	rcu_idle_exit();
}

void fake_release_cpu(void)
{
	rcu_idle_enter();
#ifdef CBMC
	(void)__sync_fetch_and_sub(&cpu_lock[smp_processor_id()], 1);
#else
	if (pthread_mutex_unlock(&cpu_lock))
		exit(-1);
#endif
	if (need_softirq) {
		need_softirq = 0;
		rcu_process_callbacks(NULL); /* cbmc recurses. */
	}
}

// Lihao
int cond_resched(void)
{
	fake_release_cpu();
	fake_acquire_cpu();
        return 1;
}

/* Interrupts */
//static int __thread local_irq_depth;
static int local_irq_depth[NR_CPUS];

void local_irq_disable()
{
	unsigned long my_cpu_id = smp_processor_id();
	if (!local_irq_depth[my_cpu_id]++) {
#ifdef CBMC
		if (__sync_fetch_and_add(&irq_lock[my_cpu_id], 1))
			SET_NOASSERT();
#else
		if (pthread_mutex_lock(&irq_lock))
			exit(-1);
#endif
	}
}

void local_irq_enable()
{
	unsigned long my_cpu_id = smp_processor_id();
	if (!--local_irq_depth[my_cpu_id]) {
#ifdef CBMC
		(void)__sync_fetch_and_sub(&irq_lock[my_cpu_id], 1);
#else
		if (pthread_mutex_unlock(&irq_lock))
			exit(-1);
#endif
	}
}

#define raw_local_irq_save(flags) local_irq_save(flags)
#define raw_local_irq_restore(flags) local_irq_restore(flags)
#define local_irq_restore(flags) local_irq_enable()
#define local_irq_save(flags) local_irq_disable()

/* Locks */
inline void mutex_init(struct mutex *m) { m->a = 0; } 
inline void mutex_lock(struct mutex *m) { m->a = 1; } 
inline void mutex_unlock(struct mutex *m) { m->a = 0; } 

inline void raw_spin_lock_init(raw_spinlock_t *lock) { *lock = 0; }
inline void spin_lock_init(spinlock_t *lock) { *lock = 0; }

void raw_spin_lock(raw_spinlock_t *lock) 
{
#ifndef CBMC
  preempt_disable();
#endif
  raw_local_irq_save(flags);
#ifdef CBMC
  __CPROVER_atomic_begin(); 
  __CPROVER_assume(*lock == 0);
  *lock = 1;
  __CPROVER_atomic_end();
#else
  *lock = 1;
#endif
  raw_local_irq_restore(flags);
}

void raw_spin_unlock(raw_spinlock_t *lock) 
{
  raw_local_irq_save(flags);
#ifdef CBMC
  __CPROVER_atomic_begin(); 
  *lock = 0;
  __CPROVER_atomic_end();
#else
  *lock = 0;
#endif
  raw_local_irq_restore(flags);
#ifndef CBMC
  preempt_enable();
#endif
}

int raw_spin_trylock(raw_spinlock_t *lock) 
{
#ifdef CBMC
  __CPROVER_atomic_begin();
#else
  preempt_disable();
#endif
  if (*lock == 0) {
     *lock = 1;
     return 1;
  }
  return 0;
#ifdef CBMC
  __CPROVER_atomic_end();
#else
  preempt_enable();
#endif
}

void raw_spin_lock_irqsave(raw_spinlock_t *lock, unsigned long flags) 
{
  local_irq_save(flags);
#ifdef CBMC
  __CPROVER_atomic_begin();
  __CPROVER_assume(*lock == 0); 
#else
  preempt_disable();
#endif
  *lock = 1;
#ifdef CBMC
  __CPROVER_atomic_end();
#endif
}

void raw_spin_unlock_irqrestore(raw_spinlock_t *lock, unsigned long flags) 
{
#ifdef CBMC
  __CPROVER_atomic_begin();
  *lock = 0; 
  __CPROVER_atomic_end();
#else
  *lock = 0;
#endif
  local_irq_restore(flags);
#ifndef CBMC
  preempt_enable();
#endif
}

void raw_spin_lock_irq(raw_spinlock_t *lock) 
{
  local_irq_disable();
#ifdef CBMC
  __CPROVER_atomic_begin();
  __CPROVER_assume(*lock == 0); 
#else
  preempt_disable();
#endif
  *lock = 1;
#ifdef CBMC
  __CPROVER_atomic_end();
#endif
}

void raw_spin_unlock_irq(raw_spinlock_t *lock) 
{
#ifdef CBMC
  __CPROVER_atomic_begin();
  *lock = 0; 
  __CPROVER_atomic_end();
#else
  *lock = 0; 
#endif
  local_irq_enable();
#ifndef CBMC
  preempt_enable();
#endif
}

int irqs_disabled_flags(unsigned long flags)
{
  return irq_lock[smp_processor_id()] > 0;
}

/* Completion */
static inline void init_completion(struct completion *x)
{
  x->a = 0;  
}

void complete(struct completion *x)
{
  x->a = 1;
}

/*
struct wait_queue_head_t {
  spinlock_t lock;
  struct list_head task_list;
};
*/

void init_waitqueue_head(wait_queue_head_t *q)
{
  //spin_lock_init(&q->lock);
  //INIT_LIST_HEAD(&q->task_list);
}

bool need_resched(void);

#define schedule_timeout_uninterruptible(delay)
#define signal_pending(current) 0
#define wake_up(x)

#define wait_event_interruptible(wq, condition) \
({                                              \
  __CPROVER_assume(condition);                  \
  1;                                            \
})

#define wait_event_interruptible_timeout(wq, condition, timeout) wait_event_interruptible(wq, condition)

// #undef CONFIG_NO_HZ_FULL
static inline bool tick_nohz_full_enabled(void) { return false; }
static inline void housekeeping_affine(struct task_struct *t) {}

#include <linux/rcupdate.h>
#ifdef TINY
#include "tiny.c"
#else
#include "update.c"
#include "tree.c"
#endif

