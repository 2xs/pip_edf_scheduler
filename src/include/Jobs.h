#ifndef __JOBS_H__
#define __JOBS_H__

#include "CNat.h"

struct embedded_coq_Entry_s {
	coq_CNat id;
	coq_CNat cnt;
	coq_CNat del;
	int next;
};

typedef struct coq_Job_s {
	coq_CNat jobid;
	coq_CNat arrival;
	coq_CNat duration;
	coq_CNat budget;
	coq_CNat deadline;
	struct embedded_coq_Entry_s entry;
	int next;
} coq_Job_t;

extern coq_Job_t JOBS_ARRAY[];
typedef coq_Job_t *coq_Job;

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
	return &(JOBS_ARRAY[job_id]);	
};

// TODO
// Maximal id of a Job
#define coq_N 5
#define SCHEDULE_PLAN {\
	{ 0,  0, 0, 0, 0, {0, 0 ,0, -1}, -1},\
	{ 1, 20, 0, 0, 0, {0, 0 ,0, -1}, -1},\
	{ 2, 30, 0, 0, 0, {0, 0 ,0, -1},  3},\
	{ 3, 30, 0, 0, 0, {0, 0 ,0, -1}, -1},\
	{ 4, 50, 0, 0, 0, {0, 0 ,0, -1}, -1}\
}
#define HYPER_PERIOD 20000

#endif
