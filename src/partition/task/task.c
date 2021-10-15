/*******************************************************************************/
/*  © Université Lille 1, The Pip Development Team (2015-2018)                 */
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

#include <stdint.h>

typedef struct __attribute__((packed)) pushad_regs_s
{
	uint32_t edi; //!< General register EDI
	uint32_t esi; //!< General register ESI
	uint32_t ebp; //!< Base pointer
	uint32_t esp; //!< Stack pointer
	uint32_t ebx; //!< General register EBX
	uint32_t edx; //!< General register EDX
	uint32_t ecx; //!< General register ECX
	uint32_t eax; //!< General register EAX
} pushad_regs_t;

typedef struct __attribute__((packed)) user_ctx_s
{
	uint32_t eip;       //!< Extended instruction pointer
	uint32_t pipflags;  //!< Flags used by PIP
	uint32_t eflags;    //!< Status register
	pushad_regs_t regs; //!< General-purpose registers
	uint32_t valid;     //!< Structure validity: 1 valid, 0 invalid
	uint32_t nfu[4];    //!< Unused
} user_ctx_t;

#define SERIAL_PORT 0x3f8
#define VIDT_VADDR  0xFFFFF000
static char Hi_str[]  = "Hi from task ";
static char hex_str[] = "0123456789ABCDEF";
static uint32_t wake_counter;
static uint32_t id;
static user_ctx_t **VIDT = (user_ctx_t **)VIDT_VADDR;

uint32_t serial_transmit_ready(void);
void serial_putc(char c);
void serial_puts(const char *str);
void decrease_counter();

void init(uint32_t initial_counter, uint32_t task_id) {
	wake_counter = initial_counter;
	id = task_id;
	// set the eip of the context to decrease_counter's address
	VIDT[0]->eip = (uint32_t) &decrease_counter;
	decrease_counter();
}

// we did not configure the VIDT to save the context after its execution,
// hence next call to the task will execute decrease_counter() as setup by init.
void decrease_counter()
{
	wake_counter--;
	serial_puts(Hi_str);
	while(!serial_transmit_ready());
	serial_putc(hex_str[id]);
	while(!serial_transmit_ready());
	serial_putc('\n');
//	while(!serial_transmit_ready());
//	serial_putc(hex_str[wake_counter]);
//	while(!serial_transmit_ready());
//	serial_putc('\n');

	// if we reached the expected termination time slot
	if(wake_counter == 0) {
		//signal termination
		asm("int %0;"
		     :
		     : "i" (100)
		);
	}
	// else busy wait for the clock interrupt
	for(;;);
}

uint32_t serial_transmit_ready(void);
void serial_putc(char c);
void serial_puts(const char *str);

uint32_t serial_transmit_ready(void) {
    register uint32_t result asm("eax");
    asm (
       "push %1;"
       "lcall $0x38,$0x0;"
       "add $0x4, %%esp;"
       /* Outputs */
       : "=r" (result)
       /* Inputs */
       : "i" (SERIAL_PORT+5)
       /* Clobbers */
       :
    );
    return result & 0x20;
}

void serial_putc(char c) {
    asm (
        "push %1;"
        "push %0;"
	"lcall $0x30, $0x0;"
	"add $0x8, %%esp"
	/* Outputs */
	:
	/* Inputs */
	: "i" (SERIAL_PORT),
	  "r" ((uint32_t) c)
	/* Clobbers */
	:
    );
}

void serial_puts(char const *const str) {
    for (char const *it = str; *it; ++it) {
	while(!serial_transmit_ready());
        serial_putc(*it);
    }
}

