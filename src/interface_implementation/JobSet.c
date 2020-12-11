#include "JobSet.h"
#include "Jobs.h"
#include "CBool.h"
#include "CNat.h"

coq_CNat JobSet_is_empty_list(coq_JobSet job_set) {
	if (job_set == -1) return true;
	return false;
}

coq_CNat JobSet_get_first_job_id(coq_JobSet job_set) {
	if (job_set == -1) return CNat_default_nat;
	return JOBS_ARRAY[job_set].id;
}

coq_CNat JobSet_get_remaining_jobs(coq_JobSet job_set) {
	if (job_set == -1) return CNat_default_nat;
	return JOBS_ARRAY[job_set].next;	
}
