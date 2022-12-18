`ifndef ID_EX_REG_GUARD
`define ID_EX_REG_GUARD

module ID_EX_REG #(parameter DATA_SIZE = 32, parameter ADDR_SIZE = 10) (
    input clk,
    input branch_id,
    input reg_write_id,
    input mem_read_id,
    input mem_write_id,
    input alu_src_id,
    input [1:0] mem_to_reg_id,
    input [1:0] AuipcLui_id,
    input [ADDR_SIZE-1:0] pc_id,
    input [DATA_SIZE-1:0] read_data_1_id,
    input [DATA_SIZE-1:0] read_data_2_id,
    input [DATA_SIZE-1:0] immediate_id,
    input [3:0] inst_30_and_14_to_12_id,
    input [4:0] inst_11_to_7_id,
    input [6:0] inst_6_to_0_id,

    output reg branch_ex,
    output reg reg_write_ex,
    output reg mem_read_ex,
    output reg mem_write_ex,
    output reg alu_src_ex,
    output reg [1:0] mem_to_reg_ex,
    output reg [1:0] AuipcLui_ex,
    output reg [ADDR_SIZE-1:0] pc_ex,
    output reg [DATA_SIZE-1:0] read_data_1_ex,
    output reg [DATA_SIZE-1:0] read_data_2_ex,
    output reg [DATA_SIZE-1:0] immediate_ex,
    output reg [3:0] inst_30_and_14_to_12_ex,
    output reg [4:0] inst_11_to_7_ex,
    output reg [6:0] inst_6_to_0_ex
);

always_ff @(posedge clk) begin 
    branch_ex <= branch_id;
    mem_read_ex <= mem_read_id;
    mem_write_ex <= mem_write_id;
    mem_to_reg_ex <= mem_to_reg_id;
    alu_src_ex <= alu_src_id;
    reg_write_ex <= reg_write_id;
    AuipcLui_ex <= AuipcLui_id;
    pc_ex <= pc_id;
    read_data_1_ex <= read_data_1_id;
    read_data_2_ex <= read_data_2_id;
    immediate_ex <= immediate_id;
    inst_30_and_14_to_12_ex <= inst_30_and_14_to_12_id;
    inst_11_to_7_ex <= inst_11_to_7_id;
    inst_6_to_0_ex <= inst_6_to_0_id;
end     

endmodule
`endif