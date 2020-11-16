#ifndef __ENTRY_H__
#define __ENTRY_H__

#include "CBool.h"
#include "CNat.h"

typedef int coq_Entry;

#define defaut_entry 0
coq_CBool Entry_is_default_entry(coq_Entry entry);

coq_CNat Entry_get_entry_counter(coq_Entry entry);
coq_CNat Entry_get_entry_id(coq_Entry entry);
coq_CNat Entry_get_entry_delete(coq_Entry entry);


coq_Entry Entry_decrease_del(coq_Entry entry);
coq_Entry Entry_decrease_cnt(coq_Entry entry);

coq_CBool Entry_cmp_entry_deadline(coq_Entry entry1, coq_Entry entry2);

coq_Entry Entry_make_entry(coq_CNat id, coq_CNat cnt, coq_CNat del);

#endif
