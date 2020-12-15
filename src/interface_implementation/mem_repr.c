#include "CBool.h"
#include "CNat.h"
#include "mem_repr.h"

internal_t INTERNAL_ARRAY[coq_N] = SCHEDULE_PLAN;
coq_CBool  JOB_DONE = false;
int JOBS_ARRIVING_HEAD_INDEX = -1;
unsigned int CLOCK = 0;
int ACTIVE_ENTRIES_HEAD_INDEX = -1;
