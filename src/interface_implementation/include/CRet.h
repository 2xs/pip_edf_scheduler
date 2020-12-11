#ifndef __CRET_H__
#define __CRET_H__

#include "CNat.h"
#include "CBool.h"

typedef struct coq_CRet_s {
       coq_CBool exists;
       coq_CBool late;
       coq_CNat job_id;
} coq_CRet;

static inline coq_CRet CRet_make_ret_type(coq_CBool exists, coq_CBool late, coq_CNat job_id) {
	coq_CRet ret_value = {exists, late, job_id};
	return ret_value;
}

#endif
