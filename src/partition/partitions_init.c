
#include <stdint.h>

#include <pip/fpinfo.h>
#include <pip/paging.h>
#include <pip/stdio.h>
#include <pip/string.h>
#include <pip/vidt.h>
#include <pip/wrappers.h>

#include "partition.h"
#include "scheduler_setup.h"
#include "mem_repr.h"

/*!
 * \brief Start address of the root partition
 * \note This symbol is defined in the link.ld file
 */
extern void *__startReadOnlyAddress;

/*!
 * \brief End address of the root partition
 * \note This symbol is defined in the link.ld file
 */
extern void *__endReadOnlyAddress;

/*!
 * \brief Symbol located at the task code's start
 * \note This symbol is defined in the link.ld file
 */
extern void *__task_code_start;

/*!
 * \brief Symbol located at the task code's start
 * \note This symbol is defined in the link.ld file
 */
extern void *__task_code_end;

/*
 * Arbitrarily chosen address where the available memory of the child will be mapped
 */
#define CHILD_AVAILABLE_MEMORY_START 0x1000000

#define NULL ((void *)0)

uint32_t JOB_ID_TO_PART_DESC[coq_N];

void boot_scheduler_partition(pip_fpinfo* boot_info);
static void print_boot_info(pip_fpinfo* boot_info);
static void setup_tasks(void);
static uint32_t create_task(uint32_t code_to_map_start, uint32_t size_code_to_map,
		            uint32_t code_load_address, uint32_t expected_task_duration);

/*!
 * \fn void init_scheduler_partition(pip_fpinfo* boot_info)
 * \brief The root partition entry point called by the 0boot.S file
 * \param bootInformation The boot information address from the ebx register
 * \warning Do not name the entry point "main" because gcc generates an
 *          erroneous machine code: it tries to retrieve the arguments argc
 *          and argv even with the parameters --freestanding and -nostdlib
 */
void boot_scheduler_partition(pip_fpinfo* boot_info)
{
	printf("The scheduler is booting ...\n");

	// Retrieve the initial context from the stack top
	user_ctx_t *initial_context = (user_ctx_t*)
	(STACK_TOP_VADDR + PAGE_SIZE - sizeof(user_ctx_t));

	if (boot_info->magic != FPINFO_MAGIC)
	{
		printf("Failed to verify boot information integrity.\n"
		       "Guru meditation\n");
		PANIC();
	}

	print_boot_info(boot_info);

	// setup a dead simple linked list "allocator"
	// to avoid hardcoding addresses
	if (!Pip_InitPaging(boot_info->membegin,
			    boot_info->memend))
	{
		printf("Failed to initialize the allocator.\n"
		       "Guru meditation\n");
		PANIC();
	}

	printf("Setting up the task partitions...\n");
	setup_tasks();

	printf("Initializing the scheduler...\n");
	init_scheduler_state();

	//previous function should not return
	PANIC();
}

static void print_boot_info(pip_fpinfo* boot_info)
{
	printf("Magic number ... 0x%x\n", boot_info->magic);
	printf("Free memory start ... 0x%x\n", boot_info->membegin);
	printf("Free memory end ... 0x%x\n", boot_info->memend);
	printf("Root partition start ... 0x%x\n", &__startReadOnlyAddress);
	printf("Root partition end ... 0x%x\n", &__endReadOnlyAddress);
	printf("Task code start ... 0x%x\n", &__task_code_start);
	printf("Task code end ... 0x%x\n", &__task_code_end);
}

/*!
 * \fn static void setup_tasks(void)
 * \brief Creates all tasks structures and partitions following the scheduling plan.
 */
static void setup_tasks(void)
{
	// Retrieve the start and end address of the task's code
	uint32_t task_code_start_addr = (uint32_t) &__task_code_start;
	uint32_t task_code_end_addr   = (uint32_t) &__task_code_end;

	// create a new task partition for every task in the schedule plan
	for (uint32_t i = 0 ; i < coq_N; i ++) {
		// Bootstrap the child partition
		uint32_t ret = create_task(task_code_start_addr,
					   task_code_end_addr - task_code_start_addr,
					   LOAD_VADDRESS,
					   // for demonstration purposes we'll take the expected duration of the task
					   i);
		switch (ret)
		{
			case 0: continue;
			case FAIL_CREATE_PARTITION:
				printf("create_task returned "
						"FAIL_CREATE_PARTITION ...\n");
				break;
			case FAIL_MAP_CHILD_PAGE:
				printf("create_task returned "
						"FAIL_MAP_CHILD_PAGE ...\n");
				break;
			case FAIL_MAP_STACK_PAGE:
				printf("create_task returned "
						"FAIL_MAP_STACK_PAGE ...\n");
				break;
			case FAIL_MAP_VIDT_PAGE:
				printf("create_task returned "
						"FAIL_MAP_VIDT_PAGE ...\n");
				break;
			default:
				printf("create_task returned "
					"an unexpected value: %d ...\n", ret);
		}
		PANIC();
	}
}

/**
 * \fn create_task(uint32_t code_to_map_start, uint32_t size_code_to_map,
                   uint32_t code_load_address, uint32_t expected_task_duration)
 * \brief creates a task partition :
 *    - creates required Pip data structures
 *    - sets up a stack and a VIDT
 *    - executable code is duplicated to other pages and then mapped into memory
 *    (i.e. original code is left untouched)
 */
static uint32_t create_task(uint32_t code_to_map_start, uint32_t size_code_to_map,
		            uint32_t code_load_address, uint32_t task_number)
{
	// Allocate 5 memory pages in order to create a child partition
	uint32_t descChild       = (uint32_t) Pip_AllocPage();
	uint32_t pdChild         = (uint32_t) Pip_AllocPage();
	uint32_t shadow1Child    = (uint32_t) Pip_AllocPage();
	uint32_t shadow2Child    = (uint32_t) Pip_AllocPage();
	uint32_t configPagesList = (uint32_t) Pip_AllocPage();

	// Create the child partition
	printf("Giving minimal pages to the kernel to create the child partition...\n");
	printf("\tdescChild : 0x%x\n", descChild);
	printf("\tpdChild   : 0x%x\n", pdChild);
	printf("\tshadow1   : 0x%x\n", shadow1Child);
	printf("\tshadow2   : 0x%x\n", shadow2Child);
	printf("\tlinkedL   : 0x%x\n", configPagesList);
	if (!Pip_CreatePartition(descChild, pdChild, shadow1Child, shadow2Child,
			configPagesList))
	{
		return FAIL_CREATE_PARTITION;
	}

	// Map each page of the child partition to the newly created partition
	printf("Mapping child's partition image into its virtual memory...\n");
	enum map_page_wrapper_ret_e map_page_rcode;
	for (uint32_t code_offset = 0; code_offset < size_code_to_map; code_offset += PAGE_SIZE)
	{
		// the tasks will share the same code for demonstration purposes
		uint32_t duplicated_code_page = (uint32_t) Pip_AllocPage();
		memcpy((void *)duplicated_code_page, (void *) (code_to_map_start + code_offset), PAGE_SIZE);
		// map the duplicated code page into the task virtual memory
		map_page_rcode = Pip_MapPageWrapper(duplicated_code_page, descChild,
						    code_load_address + code_offset);
		switch (map_page_rcode) {
			case FAIL_ALLOC_PAGE:
				printf("MapPageWrapper failed while allocating a page\n");
				return FAIL_MAP_CHILD_PAGE;
			case FAIL_PREPARE:
				printf("MapPageWrapper failed while trying to give pages to the kernel for memory data structures\n");
				return FAIL_MAP_CHILD_PAGE;
			case FAIL_ADD_VADDR:
				printf("MapPageWrapper failed while trying to add a memory page to the child\n");
				return FAIL_MAP_CHILD_PAGE;
			case SUCCESS :
				break;
			default:
				printf("Unknown MapPageWrapper return code\n");
		}
	}
	// Allocate a page for the child's stack
	printf("Allocating the child's stack...\n");
	uint32_t stackPage = (uint32_t) Pip_AllocPage();

	// Store the child's initial context at the beginning of its stack
	printf("Reserving space for the tasks's initial context in its stack...\n");
	user_ctx_t *contextPAddr = (user_ctx_t*) (stackPage + PAGE_SIZE -
						sizeof(user_ctx_t));

	printf("Reserving space for the task's expected duration...\n");
	uint32_t *arg_duration_counter_ptr = (uint32_t *) (stackPage + PAGE_SIZE -
			                     sizeof(user_ctx_t) - sizeof(uint32_t));

	printf("Setting the expected duration argument in the stack...\n");
	*arg_duration_counter_ptr = INTERNAL_ARRAY[task_number].job.duration;
	JOB_ID_TO_PART_DESC[task_number] = descChild;

	printf("Filling the task's initial context...\n");
	// Compute the virtual address of the task's context
	user_ctx_t *contextVAddr = (user_ctx_t*) (STACK_TOP_VADDR + PAGE_SIZE -
			sizeof(user_ctx_t));

	// Create the task's context
	contextPAddr->valid    = 0;
	contextPAddr->eip      = LOAD_VADDRESS;
	contextPAddr->pipflags = 0;
	contextPAddr->eflags   = 0x202;
	contextPAddr->regs.ebp = STACK_TOP_VADDR + PAGE_SIZE;
	contextPAddr->regs.esp = contextPAddr->regs.ebp - sizeof(user_ctx_t) - sizeof(uint32_t);
	contextPAddr->valid    = 1;

	// Map the stack page to the newly created partition
	printf("Mapping task's stack...\n");
	map_page_rcode = Pip_MapPageWrapper(stackPage, descChild, STACK_TOP_VADDR);
	switch (map_page_rcode) {
		case FAIL_ALLOC_PAGE:
			printf("MapPageWrapper failed while allocating a page\n");
			return FAIL_MAP_STACK_PAGE;
		case FAIL_PREPARE:
			printf("MapPageWrapper failed while trying to give pages to the kernel for memory data structures\n");
			return FAIL_MAP_STACK_PAGE;
		case FAIL_ADD_VADDR:
			printf("MapPageWrapper failed while trying to add a memory page to the task\n");
			return FAIL_MAP_STACK_PAGE;
		case SUCCESS :
			break;
		default:
			printf("Unknown MapPageWrapper return code\n");
	}

	// Allocate a memory page for the task's VIDT
	user_ctx_t **vidtPage = (user_ctx_t**) Pip_AllocPage();

	// Save the task's context into the task's VIDT
	vidtPage[0] = contextVAddr;

	// Map the VIDT page to the newly created partition
	printf("Mapping task's VIDT...\n");
	map_page_rcode = Pip_MapPageWrapper((uint32_t) vidtPage, descChild, VIDT_VADDR);
	switch (map_page_rcode) {
		case FAIL_ALLOC_PAGE:
			printf("MapPageWrapper failed while allocating a page\n");
			return FAIL_MAP_VIDT_PAGE;
		case FAIL_PREPARE:
			printf("MapPageWrapper failed while trying to give pages to the kernel for memory data structures\n");
			return FAIL_MAP_VIDT_PAGE;
		case FAIL_ADD_VADDR:
			printf("MapPageWrapper failed while trying to add a memory page to the task\n");
			return FAIL_MAP_VIDT_PAGE;
		case SUCCESS :
			break;
		default:
			printf("Unknown MapPageWrapper return code\n");
	}

	return 0;
}
