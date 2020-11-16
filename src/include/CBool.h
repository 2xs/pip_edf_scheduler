#ifndef __CBOOL_H__
#define __CBOOL_H__

#include <stdbool.h> 

typedef bool coq_CBool;

coq_CBool CBool_not(coq_CBool b);
coq_CBool CBool_and(coq_CBool b1, coq_CBool b2);

#endif
