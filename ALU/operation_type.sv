`ifndef OPERATION_TYPE_HEADER
`define OPERATION_TYPE_HEADER
typedef enum bit [3:0] { 
	ADD 					= 4'd0, 
	SUB, 					
	LESS_THAN, 				
	LESS_THAN_UNSIGNED, 
	GREATER_OR_EQUAL_THAN,  
	AND, 					
	OR, 						
	XOR, 					
	LEFT_SHIFT, 				
	LEFT_SHIFT_SIGNED, 		
	RIGHT_SHIFT,				
	RIGHT_SHIFT_SIGNED	
	} e_operations;
`endif // OPERATION_TYPE_HEADER