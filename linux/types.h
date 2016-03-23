#ifndef _LINUX_TYPES_H
#define _LINUX_TYPES_H

struct hlist_head {
        struct hlist_node *first;
};

struct hlist_node {
        struct hlist_node *next, **pprev;
};


#endif
