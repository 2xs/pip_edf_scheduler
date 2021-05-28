#include "mem_repr.h"
#include "State.h"

void State_insert_new_active_entry(coq_Entry entry, entry_cmp_func_type entry_comp_func) {
	int *entry_index_ptr = &(ACTIVE_ENTRIES_HEAD_INDEX);
	int next_index = -1;
	while (*entry_index_ptr != -1) {
		if (entry_comp_func(entry, &(INTERNAL_ARRAY[*entry_index_ptr].entry))) {
			next_index = *entry_index_ptr;
			break;
		}
		entry_index_ptr = &(INTERNAL_ARRAY[*entry_index_ptr].active_next_entry_index);
	}
	*entry_index_ptr = entry->id;
	INTERNAL_ARRAY[entry->id].active_next_entry_index = next_index;
}

void State_update_active_entries(entry_mod_func_type entry_mod_func) {
	int entry_index = ACTIVE_ENTRIES_HEAD_INDEX;
	while (entry_index != -1) {
		entry_mod_func(&(INTERNAL_ARRAY[entry_index].entry));
		entry_index = INTERNAL_ARRAY[entry_index].active_next_entry_index;
	}
}
