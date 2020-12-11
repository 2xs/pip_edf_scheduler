#ifndef __JOBSET_H__
#define __JOBSET_H__

#include "CNat.h"

typedef int coq_JobSet;

coq_CBool JobSet_is_empty_list(coq_JobSet job_set);
coq_CNat  JobSet_get_first_job_id(coq_JobSet job_set);
coq_CNat  JobSet_get_remaining_jobs(coq_JobSet job_set);

#endif
