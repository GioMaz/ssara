section .text
global _start
_start:
	jmp	L1		;
L1:
	mov	rbx,	6	;
	mov	rcx,	rbx	;
	jmp	L2		;
L2:
	mov	rbx,	rbx	;
	mov	rcx,	rcx	;
	sub	rbx,	1	;
	imul	rcx,	rbx	;
	cmp	rbx,	1	;
	jle	L3		;
	jmp	L2		;
L3:
	mov	rax,	60	;
	xor	rdi,	rdi	;
	syscall			;
