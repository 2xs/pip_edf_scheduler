#include "CBool.h"
#include "CNat.h"
#include "mem_repr.h"

internal_t INTERNAL_ARRAY[coq_N] = SCHEDULE_PLAN;
coq_CBool JOB_DONE = false;
unsigned int clock = 0;
int first_active_entry_index = -1;
