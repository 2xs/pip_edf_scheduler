#ifndef __PRIMITIVES_H__
#define __PRIMITIVES_H__

#include "CNat.h"
#include "CBool.h"
#include "JobSet.h"
#include "mem_repr.h"

static inline coq_JobSet Primitives_jobs_arriving(coq_CNat n) {
	return JOBS_ARRIVING_HEAD_INDEX;
}

static inline coq_CBool  Primitives_job_terminating(void) {
	return JOB_DONE;
}

#endif
