#ifndef __CBOOL_H__
#define __CBOOL_H__

typedef int coq_CBool;
#define bool coq_CBool
#define false 0
#define true (!false)

static inline coq_CBool CBool_not(coq_CBool b) {
	return !b;	
}

static inline coq_CBool CBool_and(coq_CBool b1, coq_CBool b2) {
	return b1 && b2;	
};

#endif
