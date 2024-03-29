`ifndef OPERATION_TYPE_HEADER
`define OPERATION_TYPE_HEADER
typedef enum bit [3:0] { 
	ADD 					= 4'd0, 
	SUB, 					
	LESS_THAN_SIGNED, 				
	LESS_THAN_UNSIGNED, 
	GREATER_OR_EQUAL_THAN_SIGNED,  
	GREATER_OR_EQUAL_THAN_UNSIGNED,  
	AND, 					
	OR, 						
	XOR, 					
	LEFT_SHIFT_SIGNED, 		
	LEFT_SHIFT_UNSIGNED, 				
	RIGHT_SHIFT_SIGNED,
	RIGHT_SHIFT_UNSIGNED			
	} e_operations;
`endif // OPERATION_TYPE_HEADER