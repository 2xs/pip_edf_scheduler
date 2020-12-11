#ifndef __JOBSET_H__
#define __JOBSET_H__

#include "CBool.h"
#include "CNat.h"
#include "mem_repr.h"

typedef int coq_JobSet;

static inline coq_CBool JobSet_is_empty_list(coq_JobSet job_set) {
	if (job_set == -1) return true;
	return false;	
};

static inline coq_CNat JobSet_get_first_job_id(coq_JobSet job_set) {
	if (job_set == -1) return CNat_default_nat;
	return job_set;	
};

static inline coq_CNat JobSet_get_remaining_jobs(coq_JobSet job_set) {
	if (job_set == -1) return CNat_default_nat;
	return INTERNAL_ARRAY[job_set].jobset_next_job_index;	
};

#endif
