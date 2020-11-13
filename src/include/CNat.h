#ifndef __CNAT_H__
#define __CNAT_H__

#include "CBool.h"

typedef coq_CNat unsigned;

#define zero 0u
#define default_nat zero

static inline coq_CBool CNat_is_default_nat(coq_CNat n) {
	return n == default_nat;
}

// I wanna die, Coq nats do not underflow (obviously).
static inline coq_CNat CNat_sub(coq_CNat n1, coq_CNat n2) {
	if (n2 > n1) return 0;
	return n1 - n2;
}

// I wanna die again, Coq nats do not underflow (obviously).
static inline coq_CNat CNat_pred(coq_CNat n) {
	if (n == 0) return 0;
	return n - 1;
}

static inline coq_CBool CNat_eqb(coq_CNat n1, coq_CNat n2) {
	return n1 == n2;
}

#endif
