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

void rcu_note_context_switch(void);
static void rcu_process_callbacks(struct softirq_action *unused);
void rcu_idle_enter(void);
void rcu_idle_exit(void);

/* Just say "no" to memory allocation. */
void kfree(const void *p)
{
}

/* Model callback wakeme_after_rcu() */
int wait_rcu_gp_flag;

// Works for a single grace period
void wait_rcu_gp(call_rcu_func_t crf)
{
	WRITE_ONCE(wait_rcu_gp_flag, 1);
	rcu_note_context_switch();
	rcu_process_callbacks(NULL);
#ifdef CBMC
	__CPROVER_assume(wait_rcu_gp_flag == 0);
#else
 	while(__sync_val_compare_and_swap(&wait_rcu_gp_flag, 0, 0));
#endif
}

void pass_rcu_gp(void) 
{
	WRITE_ONCE(wait_rcu_gp_flag, 0);
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
//int irq_lock[NR_CPUS];
//int nmi_lock[NR_CPUS];
#else
pthread_mutex_t cpu_lock[NR_CPUS];
//pthread_mutex_t irq_lock[NR_CPUS];
//pthread_mutex_t nmi_lock[NR_CPUS];
#endif

void fake_acquire_cpu(void)
{
#ifdef CBMC
	__CPROVER_atomic_begin();
	__CPROVER_assume(cpu_lock[smp_processor_id()] == 0);
	cpu_lock[smp_processor_id()] = 1;
	__CPROVER_atomic_end();
	//if (__sync_fetch_and_add(&cpu_lock[smp_processor_id()], 1))
	//	SET_NOASSERT();
#else
	if (pthread_mutex_lock(&cpu_lock[smp_processor_id()]))
		exit(-1);
#endif
	//rcu_idle_exit();
}

void fake_release_cpu(void)
{
	//rcu_idle_enter();
#ifdef CBMC
	__CPROVER_atomic_begin();
	cpu_lock[smp_processor_id()] = 0;
	__CPROVER_atomic_end();
	//(void)__sync_fetch_and_sub(&cpu_lock[smp_processor_id()], 1);
#else
	if (pthread_mutex_unlock(&cpu_lock[smp_processor_id()]))
		exit(-1);
#endif
	rcu_note_context_switch();
	//rcu_process_callbacks(NULL);
}

int cond_resched(void)
{
	return 0;

	// CBMC recurses because
	// fake_release_cpu() calls
	// rcu_process_callbacks() that
	// in turn calls cond_resched()
	//fake_release_cpu(); 
	//fake_acquire_cpu();
	// or
	//rcu_note_context_switch();
	//return 1;
}

bool need_resched(void) 
{ 
	return 0; 
} 

void resched_cpu(int cpu) 
{
}

/* Interrupts */
//static int __thread local_irq_depth;
static int local_irq_depth[NR_CPUS];

void local_irq_disable()
{
	local_irq_depth[smp_processor_id()]++;
#if 0
	if (!local_irq_depth[smp_processor_id()]++) {
#ifdef CBMC
		__CPROVER_assume(irq_lock[smp_processor_id()] == 0);	
		__sync_fetch_and_add(&irq_lock[smp_processor_id()], 1);
		//if (__sync_fetch_and_add(&irq_lock[smp_processor_id()], 1))
		//	SET_NOASSERT();
#else
		if (pthread_mutex_lock(&irq_lock[smp_processor_id()]))
			exit(-1);
#endif
	}
#endif
}

void local_irq_enable()
{
	--local_irq_depth[smp_processor_id()];
#if 0
	if (!--local_irq_depth[smp_processor_id()]) {
#ifdef CBMC
		(void)__sync_fetch_and_sub(&irq_lock[smp_processor_id()], 1);
#else
		if (pthread_mutex_unlock(&irq_lock[smp_processor_id()]))
			exit(-1);
#endif
	}
#endif
}

#define raw_local_irq_save(flags) local_irq_save(flags)
#define raw_local_irq_restore(flags) local_irq_restore(flags)
#define local_irq_save(flags) local_irq_disable()
#define local_irq_restore(flags) local_irq_enable()

/* Locks */
inline void mutex_init(struct mutex *m) 
{ 
	m->a = 0; 
} 

inline void mutex_lock(struct mutex *m) 
{ 
	__sync_fetch_and_add(&m->a, 1);
} 

inline void mutex_unlock(struct mutex *m) 
{ 
	__sync_fetch_and_sub(&m->a, 1);
} 

inline void raw_spin_lock_init(raw_spinlock_t *lock) 
{ 
	*lock = 0; 
}

inline void spin_lock_init(spinlock_t *lock) 
{ 
	*lock = 0; 
}

inline void raw_spin_lock_helper(raw_spinlock_t *lock)
{
#ifdef CBMC
	__CPROVER_atomic_begin(); 
	__CPROVER_assume(*lock == 0);
	*lock = 1;
	__CPROVER_atomic_end();
#else
	while (__sync_lock_test_and_set(lock, 1));
#endif
}

inline void raw_spin_unlock_helper(raw_spinlock_t *lock)
{
#ifdef CBMC
	__CPROVER_atomic_begin(); 
	*lock = 0;
	__CPROVER_atomic_end();
#else
	__sync_lock_release(lock);
#endif
}

void raw_spin_lock(raw_spinlock_t *lock) 
{
	preempt_disable();
	raw_spin_lock_helper(lock);
}

void raw_spin_unlock(raw_spinlock_t *lock) 
{
	raw_spin_unlock_helper(lock);
	preempt_enable();
}

int raw_spin_trylock(raw_spinlock_t *lock) 
{
	int ret;
	preempt_disable();

#ifdef CBMC
	__CPROVER_atomic_begin();
	if (*lock == 0) {
		*lock = 1;
		ret = 0;
	} else ret = 1;
	__CPROVER_atomic_end();
#else
	ret = __sync_val_compare_and_swap(lock, 0, 1);
#endif

	if (ret)
		preempt_enable();

	return ret;
}

void raw_spin_lock_irqsave(raw_spinlock_t *lock, unsigned long flags) 
{
	local_irq_save(flags);
	preempt_disable();
	raw_spin_lock_helper(lock);
}

void raw_spin_unlock_irqrestore(raw_spinlock_t *lock, unsigned long flags) 
{
	raw_spin_unlock_helper(lock);
	local_irq_restore(flags);
	preempt_enable();
}

void raw_spin_lock_irq(raw_spinlock_t *lock) 
{
	local_irq_disable();
	preempt_disable();
	raw_spin_lock_helper(lock);
}

void raw_spin_unlock_irq(raw_spinlock_t *lock) 
{
	raw_spin_unlock_helper(lock);
	local_irq_enable();
	preempt_enable();
}

int irqs_disabled_flags(unsigned long flags)
{
	return local_irq_depth[smp_processor_id()];
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


#define schedule_timeout_uninterruptible(delay)
#define signal_pending(current) 0
#define wake_up(x)

#ifdef CBMC
#define wait_event_interruptible(wq, condition) \
({                                              \
	__CPROVER_assume(condition);            \
	1;                                      \
})
#else
#define wait_event_interruptible(wq, condition) \
({                                              \
	while(!condition) {}                  	\
	1;                                      \
})
#endif

#define wait_event_interruptible_timeout(wq, condition, timeout) wait_event_interruptible(wq, condition)

// #undef CONFIG_NO_HZ_FULL
static inline bool tick_nohz_full_enabled(void) 
{ 
	return false; 
}

static inline void housekeeping_affine(struct task_struct *t) 
{
}

struct rcu_state;
bool rcu_gp_init_no_kthread(struct rcu_state *rsp);

#include <linux/rcupdate.h>
#ifdef TINY
#include "tiny.c"
#else
#include "update.c"
#include "tree.c"
#endif

#if 0
bool rcu_gp_init_no_kthread(struct rcu_state *rsp) 
{
	trace_rcu_grace_period(rsp->name,
			       READ_ONCE(rsp->gpnum),
			       TPS("reqwait"));
	rsp->gp_state = RCU_GP_WAIT_GPS;
	wait_event_interruptible(rsp->gp_wq,
				 READ_ONCE(rsp->gp_flags) &
				 RCU_GP_FLAG_INIT);
	rsp->gp_state = RCU_GP_DONE_GPS;
	/* Locking provides needed memory barrier. */
	bool ret = rcu_gp_init(rsp);
	cond_resched_rcu_qs();
#ifdef VERIFY_RCU_EXPEDITED_GP
	WRITE_ONCE(rsp->gp_activity, jiffies);
#endif
	WARN_ON(signal_pending(current));
	trace_rcu_grace_period(rsp->name,
			       READ_ONCE(rsp->gpnum),
			       TPS("reqwaitsig"));
	return ret;
}
#endif


