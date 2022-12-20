`ifndef EX_MEM_REG_GUARD
`define EX_MEM_REG_GUARD

module EX_MEM_REG #(parameter DATA_SIZE = 32, parameter ADDR_SIZE = 10) (
    input clk,
    input clear,
    input branch_ex,
    input reg_write_ex,
    input mem_read_ex,
    input mem_write_ex,
    input [1:0] mem_to_reg_ex,
    input [1:0] AuipcLui_ex,
    input [4:0] inst_11_to_7_ex,
    input [ADDR_SIZE-1:0] jump_alu_result_ex,
    input [DATA_SIZE-1:0] address_alu_result_ex,
    input address_alu_zero_ex,
    input [DATA_SIZE-1:0] read_data_2_ex,
    input [2:0] inst_14_to_12_ex,

    output reg branch_mem,
    output reg reg_write_mem,
    output reg mem_read_mem,
    output reg mem_write_mem,
    output reg [1:0] mem_to_reg_mem,
    output reg [1:0] AuipcLui_mem,
    output reg [4:0] inst_11_to_7_mem,
    output reg [ADDR_SIZE-1:0] jump_alu_result_mem,
    output reg [DATA_SIZE-1:0] address_alu_result_mem,
    output reg address_alu_zero_mem,
    output reg [DATA_SIZE-1:0] read_data_2_mem,
    output reg [2:0] inst_14_to_12_mem
    );

always_ff @(posedge clk or posedge clear) begin
    if(clear == 1) begin
        branch_mem <= 0;
        reg_write_mem <= 0;
        mem_read_mem  <= 0;
        mem_write_mem  <= 0;
        mem_to_reg_mem  <= 0;
        AuipcLui_mem  <= 0;
        inst_11_to_7_mem  <= 0;
        jump_alu_result_mem  <= 0;
        address_alu_result_mem  <= 0;
        address_alu_zero_mem  <= 0;
        read_data_2_mem <= 0;
        inst_14_to_12_mem <= 0;
    end else begin
        branch_mem <= branch_ex;
        reg_write_mem <= reg_write_ex;
        mem_read_mem <= mem_read_ex;
        mem_write_mem <= mem_write_ex;
        mem_to_reg_mem <= mem_to_reg_ex;
        AuipcLui_mem <= AuipcLui_ex;
        inst_11_to_7_mem <= inst_11_to_7_ex;
        jump_alu_result_mem <= jump_alu_result_ex;
        address_alu_result_mem <= address_alu_result_ex;
        address_alu_zero_mem <= address_alu_zero_ex;
        read_data_2_mem <= read_data_2_ex;
        inst_14_to_12_mem <= inst_14_to_12_ex;
    end
    
end 

endmodule
`endif