#include <stdio.h>

#include "CBool.h"
#include "CRet.h"
#include "EDF.h"
#include "mem_repr.h"

void set_jobs_arriving();
void update_job_counter();
void update_clock();
void print_jobs_arriving();
void print_active_entries();

unsigned int job_counter[coq_N] = { 0 };

void init_job_counter() {
	for (unsigned i = 1; i < coq_N ; i++) {
		job_counter[i] = INTERNAL_ARRAY[i].job.duration;
	}
}

int main(void) {
	coq_CRet res;
	CLOCK = 0;
	JOB_DONE = false;
	ACTIVE_ENTRIES_HEAD_INDEX = -1;
	JOBS_ARRIVING_HEAD_INDEX = -1;

	init_job_counter();

	for(unsigned int i = 0; i < 40; i++) {
		set_jobs_arriving();
		printf("--------------------------\n");
		printf("clock : %u\n", CLOCK);
		printf("jobs arriving : "); print_jobs_arriving();
		printf("active entries : "); print_active_entries();
		printf("job done : %u\n", JOB_DONE);
		printf("~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ \n");
		res = scheduler(coq_N);
		if (!res.exists) {
			printf("No job to schedule\n");
		} else {
			printf("EDF elected : %u\n", res.job_id);
			printf("      Job | arrival : %u, budget : %u, deadline : %u\n", INTERNAL_ARRAY[res.job_id].job.arrival, INTERNAL_ARRAY[res.job_id].job.budget, INTERNAL_ARRAY[res.job_id].job.deadline);
			printf("    Entry | del : %u, cnt : %u\n", INTERNAL_ARRAY[res.job_id].entry.del, INTERNAL_ARRAY[res.job_id].entry.cnt);
		}
		update_job_counter();
		update_clock();
	}
}

void print_jobs_arriving() {
	int head_index = JOBS_ARRIVING_HEAD_INDEX;
	while (head_index != -1) {
		printf("%i ", head_index);
		head_index = INTERNAL_ARRAY[head_index].jobset_next_job_index;
	}
	printf("-1\n");
}

void print_active_entries() {
	int head_index = ACTIVE_ENTRIES_HEAD_INDEX;
	while (head_index != -1) {
		printf("%i ", head_index);
		head_index = INTERNAL_ARRAY[head_index].active_next_entry_index;
	}
	printf("-1\n");
}

void set_jobs_arriving() {
	JOBS_ARRIVING_HEAD_INDEX = -1;
	int *jobset_list_ptr = &JOBS_ARRIVING_HEAD_INDEX;
	for (int i = 1; i < coq_N; i++) {
		if (INTERNAL_ARRAY[i].job.arrival == CLOCK) {
			INTERNAL_ARRAY[i].jobset_next_job_index = *jobset_list_ptr;
			JOBS_ARRIVING_HEAD_INDEX = i;
		}
	}
}

void update_job_counter() {
	if (ACTIVE_ENTRIES_HEAD_INDEX == -1) {
		JOB_DONE = 0;
		return;
	}
	JOB_DONE = !(--job_counter[ACTIVE_ENTRIES_HEAD_INDEX]);
}

void update_clock() {
	if (CLOCK == HYPER_PERIOD)
		CLOCK = 0;
}
