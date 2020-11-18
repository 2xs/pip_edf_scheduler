#include "JobSet.h"
#include "Jobs.h"
#include "CNat.h"

coq_CNat JobSet_get_length(coq_JobSet job_set){
	if (job_set == -1) return 0;
	return JobSet_get_length(JOBS_ARRAY[job_set].next) + 1;
}

coq_CNat JobSet_get_job_id(coq_JobSet job_set, coq_CNat n){
	if (job_set == -1) return default_nat;
	if (n == 0)        return job_set;
	return JobSet_get_job_id(JOBS_ARRAY[job_set].next, n - 1);	
}
