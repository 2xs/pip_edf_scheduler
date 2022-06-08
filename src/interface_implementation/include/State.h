#ifndef __STATE_H__
#define __STATE_H__

#include "CNat.h"
#include "CBool.h"
#include "Entry.h"
#include "mem_repr.h"

typedef coq_CBool (*entry_cmp_func_type) (coq_Entry e1, coq_Entry e2);
typedef coq_Entry (*entry_mod_func_type) (coq_Entry entry);

static inline coq_CNat State_get_time_counter(){
	return CLOCK;
};
static inline void State_set_time_counter(coq_CNat time_counter){
	CLOCK = time_counter;
};

static inline coq_CBool State_is_active_list_empty() {
	return (ACTIVE_ENTRIES_HEAD_INDEX == -1);
}

static inline coq_Entry State_get_first_active_entry() {
	if (ACTIVE_ENTRIES_HEAD_INDEX == -1) return default_entry;
	return &(INTERNAL_ARRAY[ACTIVE_ENTRIES_HEAD_INDEX].entry);
};

static inline void State_remove_first_active_entry() {
	if (ACTIVE_ENTRIES_HEAD_INDEX != -1) {
		ACTIVE_ENTRIES_HEAD_INDEX = INTERNAL_ARRAY[ACTIVE_ENTRIES_HEAD_INDEX].active_next_entry_index;
	}
};


static inline void State_update_first_active_entry(entry_mod_func_type entry_mod_func){
	if(ACTIVE_ENTRIES_HEAD_INDEX != -1)
		entry_mod_func(&(INTERNAL_ARRAY[ACTIVE_ENTRIES_HEAD_INDEX].entry));
}

void State_insert_new_active_entry(coq_Entry entry, entry_cmp_func_type entry_comp_func);
void State_update_active_entries(entry_mod_func_type entry_mod_func);

#endif
