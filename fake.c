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
bool wait_rcu;
void wait_rcu_gp(call_rcu_func_t crf)
{
  wait_rcu = 0;
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

static int __thread local_irq_depth;

void local_irq_save(unsigned long flags)
{
	if (!local_irq_depth++) {
#ifdef CBMC
		if (__sync_fetch_and_add(&irq_lock[smp_processor_id()], 1))
			SET_NOASSERT();
#else
		if (pthread_mutex_lock(&irq_lock))
			exit(-1);
#endif
	}
}

void local_irq_restore(unsigned long flags)
{
	if (!--local_irq_depth) {
#ifdef CBMC
		(void)__sync_fetch_and_sub(&irq_lock[smp_processor_id()], 1);
#else
		if (pthread_mutex_unlock(&irq_lock))
			exit(-1);
#endif
	}
}


#include <linux/rcupdate.h>
#ifdef TINY
#include "tiny.c"
#else
#include "update.c"
#include "tree.c"
#endif

