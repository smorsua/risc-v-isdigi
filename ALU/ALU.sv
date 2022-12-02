module ALU #(parameter SIZE = 32) (
    input [SIZE-1:0] A,
    input [SIZE-1:0] B,
    input [3:0] OPERATION,
    output reg [SIZE-1:0] RESULT,
    output ZERO
);

`include "operation_type.sv"

always_comb begin
    case(OPERATION)
        ADD: RESULT = A + B;
        SLT: RESULT = A >= B ? 0 : 1;
        SLTU: RESULT = $signed(A)>= $signed(B) ? 0 : 1;
        AND: RESULT = A & B;
        OR: RESULT = A | B;
        XOR: RESULT = A ^ B;
        LUI: RESULT  =  {B,12'd0};
        AUIPC: RESULT = {B,12'd0} + A;
        SUB: RESULT = A - B;
        BEQ: ZERO = (A == B) ? 1 : 0;
        BNE: ZERO = (A != B) ? 0 : 1;

        default: RESULT = 0;
    endcase
end

assign ZERO = RESULT == 0 ? 1'b1 : 1'b0;

endmodule

