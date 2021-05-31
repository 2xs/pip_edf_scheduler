/*******************************************************************************/
/*  © Université Lille 1, The Pip Development Team (2015-2020)                 */
/*                                                                             */
/*  This software is a computer program whose purpose is to run a minimal,     */
/*  hypervisor relying on proven properties such as memory isolation.          */
/*                                                                             */
/*  This software is governed by the CeCILL license under French law and       */
/*  abiding by the rules of distribution of free software.  You can  use,      */
/*  modify and/ or redistribute the software under the terms of the CeCILL     */
/*  license as circulated by CEA, CNRS and INRIA at the following URL          */
/*  "http://www.cecill.info".                                                  */
/*                                                                             */
/*  As a counterpart to the access to the source code and  rights to copy,     */
/*  modify and redistribute granted by the license, users are provided only    */
/*  with a limited warranty  and the software's author,  the holder of the     */
/*  economic rights,  and the successive licensors  have only  limited         */
/*  liability.                                                                 */
/*                                                                             */
/*  In this respect, the user's attention is drawn to the risks associated     */
/*  with loading,  using,  modifying and/or developing or reproducing the      */
/*  software by the user in light of its specific status of free software,     */
/*  that may mean  that it is complicated to manipulate,  and  that  also      */
/*  therefore means  that it is reserved for developers  and  experienced      */
/*  professionals having in-depth computer knowledge. Users are therefore      */
/*  encouraged to load and test the software's suitability as regards their    */
/*  requirements in conditions enabling the security of their systems and/or   */
/*  data to be ensured and,  more generally, to use and operate it in the      */
/*  same conditions as regards security.                                       */
/*                                                                             */
/*  The fact that you are presently reading this means that you have had       */
/*  knowledge of the CeCILL license and that you accept its terms.             */
/*******************************************************************************/

/*!
 * \mainpage
 * The purpose of this project is to illustrate, using a simple example, how to
 * transfer the execution flow from the root partition to a child partition.
 */

/*!
 * \file
 * This file contains the root partition source code
 */

#include <stdint.h>

#include <pip/paging.h>
#include <pip/stdio.h>
#include <pip/vidt.h>
#include <pip/wrappers.h>

#include "partition.h"
#include "EDF.h"
#include "mem_repr.h"
#include "partitions_init.h"

/*
 * Function prototypes
 */
static void yield_to_task(unsigned job_id);

void timerHandler(void);
void jobTerminationHandler(void);
static void scheduler_wfi(void);
void setup_initial_coq_state(void);
static void set_jobs_arriving(void);

uint32_t executing_job_id;

// wait for an interrupt to occur (timer)
void scheduler_wfi(void) {
	// ask pip to unmask interrupts
	Pip_Set_Int_State(1); // 0 == VCLI | 1 == VSTI
	for(;;);
}

void setup_initial_coq_state(void) {
	// clock must start at 0
	CLOCK = 0;
	// job done flag is lowered
	JOB_DONE = false;
	// no prior active_entries
	ACTIVE_ENTRIES_HEAD_INDEX = -1;
	// no prior jobs
	JOBS_ARRIVING_HEAD_INDEX = -1;
}

void set_jobs_arriving() {
	JOBS_ARRIVING_HEAD_INDEX = -1;
	int *jobset_list_ptr = &JOBS_ARRIVING_HEAD_INDEX;
	for (int i = 1; i < coq_N; i++) {
		if (INTERNAL_ARRAY[i].job.arrival == CLOCK) {
			INTERNAL_ARRAY[i].jobset_next_job_index = *jobset_list_ptr;
			JOBS_ARRIVING_HEAD_INDEX = i;
		}
	}
}

void timer_handler(void)
{
	// set links for jobs arriving at this timestamp
	set_jobs_arriving();

	// call the scheduler
	coq_CRet elected_partition = scheduler();

	if (!elected_partition.exists) {
		printf("No job to schedule, waiting...\n");
		executing_job_id = -1;
		scheduler_wfi();
	} else {
		executing_job_id = elected_partition.job_id;
		yield_to_task(JOB_ID_TO_PART_DESC[elected_partition.job_id]);
	}
}

/**
 * \brief Handler acknowledging job termination
 *        and waiting for the next interrupt
 */
void job_termination_handler(void)
{
	JOB_DONE = 1;
	scheduler_wfi();
}

void init_scheduler_state(void) {

	printf("Setting coq code expected initial state...\n");
	setup_initial_coq_state();

	printf("Setting interrupt hooks...\n");

	// Allocate two interrupt contexts
	user_ctx_t *timer_handler_ctx = Pip_AllocContext();
	user_ctx_t *job_termination_handler_ctx = Pip_AllocContext();

	// Allocate a page for the handler stack
	uint32_t handlerStackAddress = (uint32_t) Pip_AllocPage();

	// Registration of the interrupt handlers
	Pip_RegisterInterrupt(timer_handler_ctx, 32, (uint32_t) timer_handler,
			handlerStackAddress, 0);

	Pip_RegisterInterrupt(job_termination_handler_ctx, 100,
			(uint32_t) job_termination_handler,
			handlerStackAddress, 0);

	printf("Scheduler ready ! Now waiting for interrupts...\n");
	scheduler_wfi();

	// Should never be reached.
	PANIC();
}

/*!
 * \fn static void yield_to_task(void)
 * \brief Do the yield to a specific task and abort if an error occured.
 */
static void yield_to_task(unsigned job_id)
{
	uint32_t ret = Pip_Yield(job_id, 0, 0, 0, 0);

	switch (ret)
	{
		case 0: return;
		case FAIL_INVALID_INT_LEVEL:
			printf("Pip_Yield returned "
					"FAIL_INVALID_INT_LEVEL ...\n");
			break;
		case FAIL_INVALID_CTX_SAVE_INDEX:
			printf("Pip_Yield returned "
					"FAIL_INVALID_CTX_SAVE_INDEX ...\n");
			break;
		case FAIL_ROOT_CALLER:
			printf("Pip_Yield returned "
					"FAIL_ROOT_CALLER ...\n");
			break;
		case FAIL_INVALID_CHILD:
			printf("Pip_Yield returned "
					"FAIL_INVALID_CHILD ...\n");
			break;
		case FAIL_UNAVAILABLE_TARGET_VIDT:
			printf("Pip_Yield returned "
					"FAIL_UNAVAILABLE_TARGET_VIDT ...\n");
			break;
		case FAIL_UNAVAILABLE_CALLER_VIDT:
			printf("Pip_Yield returned "
					"FAIL_UNAVAILABLE_CALLER_VIDT ...\n");
			break;
		case FAIL_MASKED_INTERRUPT:
			printf("Pip_Yield returned "
					"FAIL_MASKED_INTERRUPT ...\n");
			break;
		case FAIL_UNAVAILABLE_TARGET_CTX:
			printf("Pip_Yield returned "
					"FAIL_UNAVAILABLE_TARGET_CTX ...\n");
			break;
		case FAIL_CALLER_CONTEXT_SAVE:
			printf("Pip_Yield returned "
					"FAIL_CALLER_CONTEXT_SAVE ...\n");
			break;
		default:
			printf("Pip_Yield returned an unexpected value: "
					"0x%x ...\n", ret);
	}

	PANIC();
}
