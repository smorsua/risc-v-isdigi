`ifndef IMMEDIATE_GENERATOR_GUARD
`define IMMEDIATE_GENERATOR_GUARD

`include "instruction_type.sv"

module IMMEDIATE_GENERATOR(
    input [31:0] inst,
    output reg [31:0] IMMEDIATE
);

always_comb begin
    casex(inst[6:0])
    I_FORMAT: begin
        if(inst[14:12] == 3'b101) begin
            IMMEDIATE = { 6'd0, inst[25:20] };                
        end else begin
            IMMEDIATE = { {21{inst[31]}}, inst[30:20] };
        end
    end
    
    S_FORMAT: IMMEDIATE = { {21{inst[31]}}, inst[30:25], inst[11:7] };
    B_FORMAT: IMMEDIATE = { {20{inst[31]}}, inst[7], inst[30:25], inst[11:8], 1'b0};
    U_FORMAT: IMMEDIATE = { inst[31:12], 12'b0 };
    J_FORMAT: IMMEDIATE = { {12{inst[31]}}, inst[19:12], inst[20], inst[30:21], 1'b0};
    default: IMMEDIATE = 32'd0;
    endcase
end
endmodule
`endif 