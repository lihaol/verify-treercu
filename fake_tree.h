/* config Tree RCU */
#define CONFIG_SMP
#define CONFIG_TREE_RCU
#define CONFIG_HZ_PERIODIC
#define CONFIG_RCU_FANOUT_EXACT 
#undef CONFIG_RCU_BOOST
#undef CONFIG_RCU_EXPEDITED_GP

#define NR_CPUS 2 
#define CONFIG_RCU_FANOUT_LEAF 16

#define HZ 1000

#include <linux/list.h>

#define __read_mostly
#define __must_check
#define __force
#define __noreturn

#define __MUTEX_INITIALIZER(x) { .a = 0 }
#define READ_ONCE(x) x
#define WRITE_ONCE(x, v) x = v 
#define ARRAY_SIZE(arr) (sizeof(arr) / sizeof((arr)[0]) + __must_be_array(arr))

/* multi-cores */
#define DEFINE_PER_CPU(t, name) t name[NR_CPUS]
#define DEFINE_PER_CPU_SHARED_ALIGNED(t, name) t name[NR_CPUS]

#define cpu_is_offline(c) 0
#define online_cpu(c) 1
#define cpu_online(c) 1
#define put_online_cpus() do { } while (0)
void get_online_cpus(void) {}
#define num_online_cpus() NR_CPUS

#define for_each_possible_cpu(cpu) for ((cpu) = 0; (cpu) < NR_CPUS; (cpu)++)
#define for_each_online_cpu(cpu) for ((cpu) = 0; (cpu) < NR_CPUS; (cpu)++)

#define per_cpu_ptr(p, cpu) (&(p)[cpu])
#define per_cpu(x, cpu) ((x)[cpu])


/* CBMC thread id used to refer per-cpu structures modelled by shared arrays
 * CONFIG_PREEMPT=n
 * */
extern __CPROVER_thread_local unsigned long __CPROVER_thread_id;
#define my_smp_processor_id __CPROVER_thread_id
#define raw_smp_processor_id() my_smp_processor_id
#define smp_processor_id() my_smp_processor_id


/* barriers */
#define barrier() __asm__ __volatile__("": : :"memory")
//#define smp_mb() __sync_synchronize() // Lihao
#define smp_mb() asm volatile("mfence":::"memory")
#define smp_mb__before_atomic() smp_mb()
#define smp_mb__after_atomic() smp_mb()
#define smp_wmb() barrier()

#define smp_store_release(p, v)                                         \
do {                                                                    \
        smp_mb();                                                       \
        WRITE_ONCE(*p, v);                                              \
} while (0)

#define smp_load_acquire(p)                                             \
({                                                                      \
        typeof(*p) ___p1 = READ_ONCE(*p);                               \
        smp_mb();                                                       \
        ___p1;                                                          \
})


#define __same_type(a, b) __builtin_types_compatible_p(typeof(a), typeof(b))

#define MAX_LOCKDEP_SUBCLASSES          8UL

/*
 *  * Lock-classes are keyed via unique addresses, by embedding the
 *   * lockclass-key into the kernel (or module) .data section. (For
 *    * static locks we use the lock address itself as the key.)
 *     */
struct lockdep_subclass_key {
        char __one_byte;
} __attribute__ ((__packed__));

struct lock_class_key {
        struct lockdep_subclass_key     subkeys[MAX_LOCKDEP_SUBCLASSES];
};

# define lockdep_set_class_and_name(lock, key, name) \
        do { (void)(key); (void)(name); } while (0)

/* check error utilities */
#define MAX_ERRNO       4095

#define IS_ERR_VALUE(x) unlikely((x) >= (unsigned long)-MAX_ERRNO)

static inline bool __must_check IS_ERR(__force const void *ptr)
{
        return IS_ERR_VALUE((unsigned long)ptr);
}

#define BUILD_BUG_ON(condition) ((void)sizeof(char[1 - 2*!!(condition)]))
#define BUILD_BUG_ON_ZERO(e) (sizeof(struct { int:-!!(e); }))
#define __must_be_array(a)      BUILD_BUG_ON_ZERO(__same_type((a), &(a)[0]))


/* disable trace */
#define pr_err(fmt, ...)
#define pr_alert(fmt, ...) 
#define pr_info(fmt, ...)
#define pr_cont(fmt, ...)

#define tracepoint_string(str) str
#define trace_rcu_utilization(x)
#define trace_rcu_grace_period(rcuname, gpnum, gpevent) do { } while (0)
#define trace_rcu_grace_period_init(rcuname, gpnum, level, grplo, grphi, \
                                    qsmask) do { } while (0)
#define trace_rcu_future_grace_period(rcuname, gpnum, completed, c, \
                                      level, grplo, grphi, event) \
                                      do { } while (0)
#define trace_rcu_nocb_wake(rcuname, cpu, reason) do { } while (0)
#define trace_rcu_preempt_task(rcuname, pid, gpnum) do { } while (0)
#define trace_rcu_unlock_preempted_task(rcuname, gpnum, pid) do { } while (0)
#define trace_rcu_quiescent_state_report(rcuname, gpnum, mask, qsmask, level, \
                                         grplo, grphi, gp_tasks) do { } \
        while (0)
#define trace_rcu_fqs(rcuname, gpnum, cpu, qsevent) do { } while (0)
#define trace_rcu_dyntick(polarity, oldnesting, newnesting) do { } while (0)
#define trace_rcu_prep_idle(reason) do { } while (0)
#define trace_rcu_callback(rcuname, rhp, qlen_lazy, qlen) do { } while (0)
#define trace_rcu_kfree_callback(rcuname, rhp, offset, qlen_lazy, qlen) \
        do { } while (0)
#define trace_rcu_batch_start(rcuname, qlen_lazy, qlen, blimit) \
        do { } while (0)
#define trace_rcu_invoke_callback(rcuname, rhp) do { } while (0)
#define trace_rcu_invoke_kfree_callback(rcuname, rhp, offset) do { } while (0)
#define trace_rcu_batch_end(rcuname, callbacks_invoked, cb, nr, iit, risk) \
        do { } while (0)
#define trace_rcu_torture_read(rcutorturename, rhp, secs, c_old, c) \
        do { } while (0)
#define trace_rcu_barrier(name, s, cpu, cnt, done) do { } while (0)

/* other things */
#define MODULE_ALIAS(x)
#define module_param(name, type, perm)

#define EXPORT_PER_CPU_SYMBOL(var)
#define EXPORT_PER_CPU_SYMBOL_GPL(var)

#define __releases(x)
#define early_initcall(x)
#define __stringify(x) 'x'
#define nr_context_switches() 1
void panic(const char *fmt, ...) {}

