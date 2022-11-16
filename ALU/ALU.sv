module ALU #(parameter SIZE = 32) (
    input [SIZE-1:0] A,
    input [SIZE-1:0] B,
    input [3:0] OPERATION,
    output reg [SIZE-1:0] RESULT,
    output ZERO
);

enum bit [3:0] { ADD, SUB, LESS_THAN, GREATER_OR_EQUAL_THAN, AND, OR, XNOR, LEFT_SHIFT, RIGHT_SHIFT } e_operations;

always_comb begin
    case(OPERATION)
        ADD: RESULT = A + B;
        SUB: RESULT = A - B; 
        LESS_THAN: RESULT = A < B;
        GREATER_OR_EQUAL_THAN: RESULT = A >= B;
        AND: RESULT = A & B;
        OR: RESULT = A | B;
        XNOR: RESULT = A ^ B;
        LEFT_SHIFT: RESULT = A << B;
        RIGHT_SHIFT: RESULT = A >> B;
        default: RESULT = 0;
    endcase 
end

assign ZERO = RESULT == 0 ? 1'b1 : 1'b0;

endmodule