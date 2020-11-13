#ifndef __STATE_H__
#define __STATE_H__

#include "CNat.h"
#include "CBool.h"

typedef coq_CBool (*entry_cmp_func_type) (coq_Entry, coq_Entry);
typedef coq_Entry (*entry_mod_func_type) (coq_Entry);

coq_CNat State_get_time_counter();
void State_set_time_counter(coq_CNat time_counter);

coq_Entry State_get_first_active_entry();
void State_remove_first_entry();
void State_insert_new_active_entry(coq_Entry entry, entry_cmp_func_type entry_comp_func);
void State_update_first_active_entry(entry_mod_func_type entry_mod_func);
void State_update_active_entries(entry_mod_func_type entry_mod_func);

#endif
