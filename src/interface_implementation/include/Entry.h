#ifndef __ENTRY_H__
#define __ENTRY_H__

#include "CBool.h"
#include "CNat.h"
#include "mem_repr.h"

typedef struct __internal_entry__ *coq_Entry;

#define default_entry (&(INTERNAL_ARRAY[0].entry))
static inline coq_CBool Entry_is_default_entry(coq_Entry entry) {
	return entry == default_entry;	
};

static inline coq_CNat Entry_get_entry_counter(coq_Entry entry) {
	return entry->cnt;
};

static inline coq_CNat Entry_get_entry_id(coq_Entry entry) {
	return entry->id;	
};

static inline coq_CNat Entry_get_entry_delete(coq_Entry entry){
	return entry->del;	
};


static inline coq_Entry Entry_decrease_del(coq_Entry entry) {
	(entry->del)--;
	return entry;
};
static inline coq_Entry Entry_decrease_cnt(coq_Entry entry) {
	(entry->cnt)--;
	return entry;
};

static inline coq_CBool Entry_cmp_entry_deadline(coq_Entry entry1, coq_Entry entry2) {
	return entry1->del < entry2->del;
};

static inline coq_Entry Entry_make_entry(coq_CNat id, coq_CNat cnt, coq_CNat del) {
	coq_Entry entry = &(INTERNAL_ARRAY[id].entry);
	entry->id = id;
	entry->cnt = cnt;
	entry->del = del;
	return entry;	
};

#endif
