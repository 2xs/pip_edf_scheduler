#include "mem_repr.h"
#include "State.h"

void State_insert_new_active_entry(coq_Entry entry, entry_cmp_func_type entry_comp_func) {
	// if no active entry
	if (ACTIVE_ENTRIES_HEAD_INDEX == -1) {
		ACTIVE_ENTRIES_HEAD_INDEX = entry->id;
		INTERNAL_ARRAY[entry->id].active_next_entry_index = -1;
	} else {
		int current_entry_index = ACTIVE_ENTRIES_HEAD_INDEX;
		int *previous_entry_index_ptr = &ACTIVE_ENTRIES_HEAD_INDEX;
		while (current_entry_index != -1) {
			bool cmp_result = entry_comp_func(entry, &(INTERNAL_ARRAY[current_entry_index].entry));
			if (cmp_result) {
				INTERNAL_ARRAY[entry->id].active_next_entry_index = current_entry_index;
				*previous_entry_index_ptr = entry->id;
			}
			else {
				previous_entry_index_ptr = &(INTERNAL_ARRAY[current_entry_index].active_next_entry_index);
				current_entry_index = INTERNAL_ARRAY[current_entry_index].active_next_entry_index;
			}
		}
	}
}

void State_update_active_entries(entry_mod_func_type entry_mod_func) {
	int current_entry_index = ACTIVE_ENTRIES_HEAD_INDEX;
	while (current_entry_index != -1) {
		entry_mod_func(&(INTERNAL_ARRAY[current_entry_index].entry));
		current_entry_index = INTERNAL_ARRAY[current_entry_index].active_next_entry_index;
	}
}
