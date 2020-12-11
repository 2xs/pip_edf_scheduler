#include "State.h"

unsigned int clock = 0;
int first_active_entry = -1;

void State_insert_new_active_entry(coq_Entry entry, entry_cmp_func_type entry_comp_func) {
	if (first_active_entry == -1) {
		first_active_entry = entry->job_id;
		entry.next = -1;
	} else {
		int current_entry = first_active_entry;
		int *previous_entry_id = &first_active_entry;
		while (current_entry != -1) {
			bool cmp_result = entry_comp_func(entry, &(JOBS_ARRAY[current_entry].entry));
			if (cmp_result) {
				entry->next = current_entry;
				*previous_entry_id = entry->id;
			}
			else {
				previous_entry_id = &(JOBS_ARRAY[current_entry].entry.next);
				current_entry = JOBS_ARRAY[current_entry].entry.next;
			}
		}
	}
}

void State_update_active_entries(entry_mod_func_type entry_mod_func) {
	int current_entry = first_active_entry;
	while (current_entry != -1) {
		entry_mod_func(&(JOBS_ARRAY[current_entry].entry));
		current_entry = JOBS_ARRAY[current_entry].entry.next;
	}
}
