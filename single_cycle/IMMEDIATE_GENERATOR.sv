module IMMEDIATE_GENERATOR(
    input [31:0] inst,
    output [31:0] IMMEDIATE
);
`include "instruction_type.sv"

always_comb begin
    case(inst[0:6])
    I_FORMAT: IMMEDIATE = { 21{inst[31]} , inst[30:20] };
    S_FORMAT: IMMEDIATE = { 21{inst[31]}, inst[30:25], inst[11:7] };
    B_FORMAT: IMMEDIATE = { 20{inst[31]}, inst[7], inst[30:25], inst[11:8], 1'b0};
    U_FORMAT: IMMEDIATE = { inst[31:12], 12'b0 };
    J_FORMAT: IMMEDIATE = { 12{inst[31]}, inst[19:12], inst[20], inst[30:21], 1'b0};
    default:
    endcase
end
endmodule
