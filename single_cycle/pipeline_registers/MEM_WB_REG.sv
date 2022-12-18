`ifndef MEM_WB_REG_GUARD
`define MEM_WB_REG_GUARD

module MEM_WB_REG #(parameter DATA_SIZE = 32) (
    input clk,
    input [1:0] mem_to_reg_mem,
    input reg_write_mem,
    input [DATA_SIZE-1:0] ddata_r_mem,
    input [DATA_SIZE-1:0] address_alu_result_mem,
    input [4:0] inst_11_to_7_mem,

    output reg [1:0] mem_to_reg_wb,
    output reg reg_write_wb,
    output [DATA_SIZE-1:0] ddata_r_wb,
    output reg [DATA_SIZE-1:0] address_alu_result_wb,
    output reg [4:0] inst_11_to_7_wb
);

always_ff @(posedge clk) begin
    mem_to_reg_wb <= mem_to_reg_mem;
    reg_write_wb <= reg_write_mem;
    address_alu_result_wb <= address_alu_result_mem;
    inst_11_to_7_wb <= inst_11_to_7_mem;
end

assign ddata_r_wb = ddata_r_mem;

endmodule
`endif