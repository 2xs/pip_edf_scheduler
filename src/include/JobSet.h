#ifndef __JOBSET_H__
#define __JOBSET_H__

#include "CNat.h"

typedef coq_JobSet int;

coq_CNat JobSet_get_job_id(coq_JobSet job_set, coq_CNat n);
coq_CNat JobSet_get_length(coq_JobSet job_set);

#endif
