#ifndef __STATE_H__
#define __STATE_H__

#include "CNat.h"
#include "CBool.h"
#include "Entry.h"

extern coq_CNat clock;
extern int first_active_entry_index;

typedef coq_CBool (*entry_cmp_func_type) (coq_Entry e1, coq_Entry e2);
typedef coq_Entry (*entry_mod_func_type) (coq_Entry entry);

static inline coq_CNat State_get_time_counter(){
	return clock;	
};
static inline void State_set_time_counter(coq_CNat time_counter){
	clock = time_counter;	
};

static inline coq_CBool State_is_active_list_empty() {
	return (first_active_entry_index == -1);
}

static inline coq_Entry State_get_first_active_entry() {
	if (first_active_entry_index == -1) return default_entry;
	return &(INTERNAL_ARRAY[first_active_entry_index].entry);
};

static inline void State_remove_first_active_entry() {
	if (first_active_entry_index != -1) {
		first_active_entry_index = INTERNAL_ARRAY[first_active_entry_index].active_next_entry_index;
	}
};


static inline void State_update_first_active_entry(entry_mod_func_type entry_mod_func){
	entry_mod_func(&(INTERNAL_ARRAY[first_active_entry_index].entry));	
};

void State_insert_new_active_entry(coq_Entry entry, entry_cmp_func_type entry_comp_func);
void State_update_active_entries(entry_mod_func_type entry_mod_func);

#endif
