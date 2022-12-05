`ifndef OPERATION_TYPE_HEADER
`define OPERATION_TYPE_HEADER
typedef enum { 
	ADD	= 'd0, 
	SLT	= 'd1, 
	SLTU	= 'd2,
	AND	= 'd3, 
	OR		= 'd4, 
	XOR	= 'd5,
	LUI	= 'd6, 
	AUIPC	= 'd7, 
	SUB	= 'd8, 
	BEQ	= 'd9, 
	BNE	= 'd10,
	LW		= 'd11, 
	SW		= 'd12 
} e_operations;
`endif //OPERATION_TYPE_HEADER