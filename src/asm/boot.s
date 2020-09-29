.section  .text
.global  boot
.extern  main
.extern  Pip_VCLI

boot:
	/* Push  EBX  onto  the  stack */
	push %ebx
	/*  Disable  interrupts  */
	call  Pip_VCLI
	/* Call  main */
	call  main
	/*  Fallback  */
loop:
	jmp  loop
