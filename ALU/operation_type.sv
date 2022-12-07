`ifndef OPERATION_TYPE_HEADER
`define OPERATION_TYPE_HEADER
typedef enum bit [3:0] { 
	ADD 					= 4'd0, 
	SUB 					= 4'd1, 
	LESS_THAN 				= 4'd2, 
	GREATER_OR_EQUAL_THAN 	= 4'd3,  
	AND 					= 4'd4,
	OR 						= 4'd5, 
	XOR 					= 4'd6, 
	LEFT_SHIFT 				= 4'd7, 
	SIGNED_LEFT_SHIFT 		= 4'd8, 
	RIGHT_SHIFT 			= 4'd9, 
	SIGNED_RIGHT_SHIFT		= 4'd10
	} e_operations;
`endif // OPERATION_TYPE_HEADER