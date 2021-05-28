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
 * \file
 * This file contains the constant definition used by the root partition
 */

#ifndef __DEF_PARTITION_H__
#define __DEF_PARTITION_H__

/*!
 * \def FAIL_CREATE_PARTITION
 * \brief Create partition error code
 */
#define FAIL_CREATE_PARTITION	 1

/*!
 * \def FAIL_MAP_CHILD_PAGE
 * \brief Map child page error code
 */
#define FAIL_MAP_CHILD_PAGE	 2

/*!
 * \def FAIL_MAP_STACK_PAGE
 * \brief Map stack page error code
 */
#define FAIL_MAP_STACK_PAGE	3

/*!
 * \def FAIL_MAP_VIDT_PAGE
 * \brief Map VIDT page error code
 */
#define FAIL_MAP_VIDT_PAGE	4

/*!
 * \def FAIL_INVALID_INT_LEVEL
 * \brief Invalid interrupt level error code
 */
#define FAIL_INVALID_INT_LEVEL		1

/*!
 * \def FAIL_INVALID_CTX_SAVE_INDEX
 * \brief Invalid context save index error code
 */
#define FAIL_INVALID_CTX_SAVE_INDEX	2

/*!
 * \def FAIL_ROOT_CALLER
 * \brief Root caller error code
 */
#define FAIL_ROOT_CALLER		3

/*!
 * \def FAIL_INVALID_CHILD
 * \brief Invalid child error code
 */
#define FAIL_INVALID_CHILD		4

/*!
 * \def FAIL_UNAVAILABLE_TARGET_VIDT
 * \brief Unavailable VIDT target error code
 */
#define FAIL_UNAVAILABLE_TARGET_VIDT	5

/*!
 * \def FAIL_UNAVAILABLE_CALLER_VIDT
 * \brief Unavailable VIDT caller error code
 */
#define FAIL_UNAVAILABLE_CALLER_VIDT	6

/*!
 * \def FAIL_MASKED_INTERRUPT
 * \brief Masked interrupt error code
 */
#define FAIL_MASKED_INTERRUPT		7

/*!
 * \def FAIL_UNAVAILABLE_TARGET_CTX
 * \brief Unavailable target context error code
 */
#define FAIL_UNAVAILABLE_TARGET_CTX	8

/*!
 * \def FAIL_CALLER_CONTEXT_SAVE
 * \brief Caller context save error code
 */
#define FAIL_CALLER_CONTEXT_SAVE	9

/*!
 * \def BOOTINFO_VADDR
 * \brief The boot informations address
 */
#define BOOTINFO_VADDR	0xffffc000

/*!
 * \def STACK_TOP_VADDR
 * \brief The stack top address
 */
#define STACK_TOP_VADDR 0xffffe000

/*!
 * \def LOAD_VADDRESS
 * \brief The virtual address where to load the child
 */
#define LOAD_VADDRESS	0x700000

/*!
 * \def PANIC()
 * \brief The macro used for unexpected behavior
 */
#define PANIC()				\
	do {				\
		printf("Panic!\n");	\
		for (;;);		\
	} while (0)

#endif
