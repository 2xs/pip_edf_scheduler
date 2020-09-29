OUTPUT_FORMAT("binary")
ENTRY(boot)

SECTIONS
{
	.text 0x700000 : /*  Partition  load  address  */
	{
		text = .; _text = .;  __text = .;
		*(.text)
		. = ALIGN(0x1000); /* Page -align  sections  */
	}
	
	.data :
	{
		data = .;  _data = .;  __data = .;
		*(.data)
		*(.rodata)
		. = ALIGN (0x1000);
	}
	
	.bss :
	{
		bss = .; _bss = .;  __bss = .;
		*(.bss)
	}

	end = .; _end = .;  __end = .;
}
