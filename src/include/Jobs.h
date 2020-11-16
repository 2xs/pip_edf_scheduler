#ifndef __JOBS_H__
#define __JOBS_H__

#include "CNat.h"

typedef int coq_Job;

coq_CNat Jobs_get_budget(coq_Job job);
coq_CNat Jobs_get_arrival(coq_Job job);
coq_CNat Jobs_get_deadline(coq_Job job);

coq_Job Jobs_get_job_from_job_id(coq_CNat job_id);

#endif
