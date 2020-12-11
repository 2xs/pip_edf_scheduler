#ifndef __PRIMITIVES_H__
#define __PRIMITIVES_H__

#include "CNat.h"
#include "CBool.h"
#include "JobSet.h"

coq_JobSet Primitives_jobs_arriving(coq_CNat n);
coq_CBool  Primitives_job_terminating(void);

#endif
