module IMMEDIATE_GENERATOR(
    input [31:0] inst,
    output [31:0] IMMEDIATE
);
//TODO: mover enum de tipos de instrucciones a archivo global.
enum { 
    I_FORMAT = 'b0010011, 
    S_FORMAT = 'b0100011, 
    B_FORMAT = 'b1100011,
    U_FORMAT = 'b0110111,
    J_FORMAT = 'b1101111
    } instruction_type;

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
