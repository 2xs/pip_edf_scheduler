#include <stdio.h>

#include "CBool.h"
#include "CRet.h"
#include "EDF.h"
#include "mem_repr.h"

void set_jobs_arriving();
void update_clock();

int main(void) {
	coq_CRet res;
	CLOCK = 0;
	JOB_DONE = false;
	ACTIVE_ENTRIES_HEAD_INDEX = -1;
	JOBS_ARRIVING_HEAD_INDEX = -1;

	for(unsigned int i = 0; i < 40; i++) {
		set_jobs_arriving();
		printf("--------------------------\n");
		printf("clock : %u\n", CLOCK);
		printf("jobs arriving head : %i\n", JOBS_ARRIVING_HEAD_INDEX);
		printf("active entries head : %i\n", ACTIVE_ENTRIES_HEAD_INDEX);

		printf("~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ \n");
		res = scheduler(coq_N);
		if (!res.exists) {
			printf("No job to schedule\n");
		} else {
			printf("EDF elected : %u\n", res.job_id);
			printf("JOB | arrival : %u, budget : %u, deadline : %u\n", INTERNAL_ARRAY[res.job_id].job.arrival, INTERNAL_ARRAY[res.job_id].job.budget, INTERNAL_ARRAY[res.job_id].job.deadline);
			printf("    | del : %u, cnt : %u\n", INTERNAL_ARRAY[res.job_id].entry.del, INTERNAL_ARRAY[res.job_id].entry.cnt);
		}
		update_clock();
	}
}


void set_jobs_arriving() {
	JOBS_ARRIVING_HEAD_INDEX = -1;
	int *jobset_list_ptr = &JOBS_ARRIVING_HEAD_INDEX;
	for (int i = 1; i < coq_N; i++) {
		if (INTERNAL_ARRAY[i].job.arrival == CLOCK) {
			INTERNAL_ARRAY[i].jobset_next_job_index = *jobset_list_ptr;
			jobset_list_ptr = &(INTERNAL_ARRAY[i].jobset_next_job_index);
			JOBS_ARRIVING_HEAD_INDEX = i;
		}
	}
}

void update_clock() {
	if (CLOCK == HYPER_PERIOD)
		CLOCK = 0;
}
