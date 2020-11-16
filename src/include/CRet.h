#ifndef __CRET_H__
#define __CRET_H__

#include "CNat.h"
#include "CBool"

typedef int coq_CRet;

coq_CRet CRet_make_ret_type(coq_CBool exist, coq_CBool late, coq_CNat job_id);

#endif
