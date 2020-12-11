#ifndef __JOBS_H__
#define __JOBS_H__

#include "CNat.h"
#include "mem_repr.h"

typedef struct __internal_job__ *coq_Job;

static inline coq_CNat Jobs_get_budget(coq_Job job) {
	return job->budget;
};
static inline coq_CNat Jobs_get_arrival(coq_Job job){
	return job->arrival;
};
static inline coq_CNat Jobs_get_deadline(coq_Job job) {
	return job->deadline;
};

static inline coq_Job Jobs_get_job_from_job_id(coq_CNat job_id) {
	return &(INTERNAL_ARRAY[job_id].job);
};

#endif
