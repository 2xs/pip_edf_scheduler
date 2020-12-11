#ifndef __MEM_REPR__
#define __MEM_REPR__

#include "CBool.h"
#include "CNat.h"

struct __internal_entry__ {
	coq_CNat id;
	coq_CNat cnt;
	coq_CNat del;
};

struct __internal_job__ {
	coq_CNat job_id;
	coq_CNat arrival;
	coq_CNat duration;
	coq_CNat budget;
	coq_CNat deadline;
};

typedef struct __internal_s__ {
	struct __internal_job__   job;
	struct __internal_entry__ entry;
	int jobset_next_job_index;
	int active_next_entry_index;
} internal_t;

extern internal_t INTERNAL_ARRAY[];
extern coq_CBool  JOB_DONE;
extern unsigned int clock;
extern int first_active_entry_index;

// FIXME
// Maximal id of a Job
#define coq_N 5

/* Implementation requirements :
 *     - entry.id and job.job_id should be equal to index in SCHEDULE_PLAN array
 */
#define SCHEDULE_PLAN {                        \
	{ {0,  0, 0, 0, 0}, {0, 0 ,0}, -1, -1},\
	{ {1, 20, 0, 0, 0}, {0, 0 ,0}, -1, -1},\
	{ {2, 30, 0, 0, 0}, {0, 0 ,0},  3, -1},\
	{ {3, 30, 0, 0, 0}, {0, 0 ,0}, -1, -1},\
	{ {4, 50, 0, 0, 0}, {0, 0 ,0}, -1, -1} \
}
#define HYPER_PERIOD 20000

#endif
