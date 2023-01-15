`ifndef PIPELINED_GUARD
`define PIPELINED_GUARD

`include "../Shared/MUX.sv"
`include "../Shared/ALU/ALU.sv"
`include "../Shared/ALU/operation_type.sv"
`include "../Shared/Control/ALU_CONTROL.sv"
`include "../Shared/Control/CONTROL.sv"
`include "../Shared/Control/IMMEDIATE_GENERATOR.sv"
`include "../Shared/Control/instruction_type.sv"

`include "./banco_registros/banco_registros_registered.sv"
`include "./memories/ram_registered.sv"
`include "./memories/rom_registered.sv"

`include "./pipelined_registers/IF_ID_REG.sv"
`include "./pipelined_registers/ID_EX_REG.sv"
`include "./pipelined_registers/EX_MEM_REG.sv"
`include "./pipelined_registers/MEM_WB_REG.sv"

module pipelined
#(parameter DATA_SIZE = 32, parameter ADDR_SIZE = 10)(
    input                   CLK,
    input                   RESET_N,
    input                   CLEAR,
    input  [DATA_SIZE-1:0]  idata,
    output [ADDR_SIZE-1:0]  iaddr,
    output [ADDR_SIZE-1:0]  daddr,
    input  [DATA_SIZE-1:0]  ddata_r,
    output [DATA_SIZE-1:0]  ddata_w,
    output mem_write, mem_read,
    output [DATA_SIZE-1:0] reg_write_data,
    output reg_write_enable,
    output [4:0] write_register
);

logic [ADDR_SIZE-1+2:0] next_pc_wire;

bit [ADDR_SIZE -1 + 2:0] PC;


always_ff @(posedge CLK or negedge RESET_N) begin
    if(RESET_N == 0) begin
        PC <= 0;
    end else begin
        PC <= next_pc_wire;
    end
end

logic [ADDR_SIZE - 1 + 2:0] next_consecutive_pc_wire;
ALU #(.SIZE(ADDR_SIZE + 2)) pc_alu(
    .A(PC),
    .B(12'd4),
    .OPERATION(ADD),
    .RESULT(next_consecutive_pc_wire),
    .ZERO()
);

assign iaddr = PC[11:2];

logic [ADDR_SIZE-1+2:0] pc_id;
logic [DATA_SIZE-1:0] inst_id;
IF_ID_REG #(.DATA_SIZE(DATA_SIZE), .ADDR_SIZE(ADDR_SIZE)) if_id_reg(
    .clk(CLK),
    .clear(CLEAR),
    .pc_if(PC),
    .inst_if(idata),
    .pc_id(pc_id),
    .inst_id(inst_id)
);

logic branch_id, reg_write_id, mem_read_id, mem_write_id, alu_src_id;
logic [1:0] mem_to_reg_id;
logic [1:0] AuipcLui_id;
CONTROL control(
    .OPCODE(inst_id[6:0]),
    .BRANCH(branch_id),
    .REG_WRITE(reg_write_id),
    .MEM_READ(mem_read_id),
    .MEM_WRITE(mem_write_id),
    .ALU_SRC(alu_src_id),
    .MEM_TO_REG(mem_to_reg_id),
    .AuipcLui(AuipcLui_id)
);

logic [DATA_SIZE-1:0] read_data_1_id, read_data_2_id;
logic [DATA_SIZE-1:0] data_mux_result_wire;
logic reg_write_wb;
logic [4:0] inst_11_to_7_wb;

banco_registros_registered #(.SIZE(DATA_SIZE)) registros(
    .CLK(CLK),
    .RESET_N(RESET_N),
    .read_reg1(inst_id[19:15]),
    .read_reg2(inst_id[24:20]),
    .write_reg(inst_11_to_7_wb),
    .writeData(data_mux_result_wire),
    .RegWrite(reg_write_wb),
    .Data1(read_data_1_id),
    .Data2(read_data_2_id)
);

assign reg_write_enable = reg_write_wb;
assign write_register = inst_11_to_7_wb;

logic [DATA_SIZE-1:0] immediate_id;
IMMEDIATE_GENERATOR imm_gen(
    .inst(inst_id),
    .IMMEDIATE(immediate_id)
);

logic branch_ex, reg_write_ex, mem_read_ex, mem_write_ex, alu_src_ex;
logic [1:0] mem_to_reg_ex, AuipcLui_ex;
logic [ADDR_SIZE-1+2:0] pc_ex;
logic [DATA_SIZE-1:0] read_data_1_ex, read_data_2_ex, immediate_ex;
logic [3:0] inst_30_and_14_to_12_ex;
logic [4:0] inst_11_to_7_ex;
logic [6:0] inst_6_to_0_ex;
logic [4:0] inst_19_to_15_ex, inst_24_to_20_ex;
ID_EX_REG id_ex_reg(
    .clk(CLK),
    .clear(CLEAR),
    .branch_id(branch_id),
    .reg_write_id(reg_write_id),
    .mem_read_id(mem_read_id),
    .mem_write_id(mem_write_id),
    .alu_src_id(alu_src_id),
    .mem_to_reg_id(mem_to_reg_id),
    .AuipcLui_id(AuipcLui_id),
    .pc_id(pc_id),
    .read_data_1_id(read_data_1_id),
    .read_data_2_id(read_data_2_id),
    .immediate_id(immediate_id),
    .inst_30_and_14_to_12_id({inst_id[30], inst_id[14:12]}),
    .inst_11_to_7_id(inst_id[11:7]),
    .inst_6_to_0_id(inst_id[6:0]),
    .inst_19_to_15_id(inst_id[19:15]),
    .inst_24_to_20_id(inst_id[24:20]),

    .branch_ex(branch_ex),
    .reg_write_ex(reg_write_ex),
    .mem_read_ex(mem_read_ex),
    .mem_write_ex(mem_write_ex),
    .alu_src_ex(alu_src_ex),
    .mem_to_reg_ex(mem_to_reg_ex),
    .AuipcLui_ex(AuipcLui_ex),
    .pc_ex(pc_ex),
    .read_data_1_ex(read_data_1_ex),
    .read_data_2_ex(read_data_2_ex),
    .immediate_ex(immediate_ex),
    .inst_30_and_14_to_12_ex(inst_30_and_14_to_12_ex),
    .inst_11_to_7_ex(inst_11_to_7_ex),
    .inst_6_to_0_ex(inst_6_to_0_ex),
    .inst_19_to_15_ex(inst_19_to_15_ex),
    .inst_24_to_20_ex(inst_24_to_20_ex)
);

logic [1:0] forwardA, forwardB;
logic [DATA_SIZE-1:0] second_operand_wire;
logic [DATA_SIZE-1:0] myInput_alu_src_2_mux[2];

logic [4:0] inst_11_to_7_wb_aux;
logic reg_write_wb_aux;
logic data_mux_result_wire_aux;

assign myInput_alu_src_2_mux[0] = read_data_2_ex;
assign myInput_alu_src_2_mux[1] = immediate_ex;
MUX #(.SIZE(DATA_SIZE), .INPUTS(2)) alu_src_2_mux (
    .all_inputs(myInput_alu_src_2_mux),
    .sel(alu_src_ex),
    .result(second_operand_wire)
);

logic [3:0] ALUSelection_wire;
ALU_CONTROL alu_control(
    .OPCODE(inst_6_to_0_ex),
    .funct3(inst_30_and_14_to_12_ex[2:0]),
    .bit30(inst_30_and_14_to_12_ex[3]),
    .ALUSelection(ALUSelection_wire)
);
logic [DATA_SIZE-1:0] address_alu_result_mem;
logic [DATA_SIZE-1:0] forwardA_mux [4];
logic [DATA_SIZE-1:0] result_fordwardA;
assign forwardA_mux [0] = read_data_1_ex;
assign forwardA_mux [1] = data_mux_result_wire;
assign forwardA_mux [2] =  address_alu_result_mem;
assign forwardA_mux [3] = data_mux_result_wire_aux;
MUX #(.SIZE(DATA_SIZE), .INPUTS(4)) forwardAmux(
    .all_inputs(forwardA_mux),
    .sel(forwardA),
    .result(result_fordwardA)
);

logic [DATA_SIZE-1:0] forwardB_mux [4];
logic [DATA_SIZE-1:0] result_fordwardB;
assign forwardB_mux [0] = second_operand_wire;
assign forwardB_mux [1] = data_mux_result_wire;
assign forwardB_mux [2] =  address_alu_result_mem;
assign forwardB_mux [3] = data_mux_result_wire_aux;
MUX #(.SIZE(DATA_SIZE), .INPUTS(4)) forwardBmux(
    .all_inputs(forwardB_mux),
    .sel(forwardB),
    .result(result_fordwardB)
);

logic [DATA_SIZE-1:0] address_alu_result_ex;
logic address_alu_zero_ex;
ALU #(.SIZE(DATA_SIZE)) address_alu(
    .A(result_fordwardA),
    .B(result_fordwardB),
    .OPERATION(ALUSelection_wire),
    .RESULT(address_alu_result_ex),
    .ZERO(address_alu_zero_ex)
);

logic [ADDR_SIZE-1+2:0] jump_alu_result_ex;
ALU #(.SIZE(ADDR_SIZE+2)) jump_alu(
    .A(pc_ex),
    .B(immediate_ex[11:0]),
    .OPERATION(ADD),
    .RESULT(jump_alu_result_ex),
    .ZERO()
);

logic [4:0] inst_11_to_7_mem;
data_forwarding #(.SIZE(DATA_SIZE)) data_forwarding(
    .reg_write_mem(reg_write_mem), 
    .reg_write_ex(reg_write_ex),
    .reg_write_wb(reg_write_wb),
    .reg_write_wb_aux(reg_write_wb_aux),
    .inst_11_to_7_mem(inst_11_to_7_mem),
    .inst_11_to_7_wb(inst_11_to_7_wb),
    .inst_11_to_7_wb_aux(inst_11_to_7_wb_aux),
    .inst_19_to_15_ex(inst_19_to_15_ex),
    .inst_24_to_20_ex(inst_24_to_20_ex),
    .forwardA(forwardA),
    .forwardB(forwardB)
);
logic branch_mem, mem_read_mem, mem_write_mem;
logic [1:0] mem_to_reg_mem, AuipcLui_mem;
logic [DATA_SIZE-1:0] read_data_2_mem;
logic [ADDR_SIZE-1+2:0] jump_alu_result_mem;
logic [2:0] inst_14_to_12_mem;
logic address_alu_zero_mem;
EX_MEM_REG #(.DATA_SIZE(32), .ADDR_SIZE(10)) ex_mem_reg  (
    .clk(CLK),
    .clear(CLEAR),
    .branch_ex(branch_ex),
    .reg_write_ex(reg_write_ex),
    .mem_read_ex(mem_read_ex),
    .mem_write_ex(mem_write_ex),
    .mem_to_reg_ex(mem_to_reg_ex),
    .AuipcLui_ex(AuipcLui_ex),
    .inst_11_to_7_ex(inst_11_to_7_ex),
    .jump_alu_result_ex(jump_alu_result_ex),
    .address_alu_result_ex(address_alu_result_ex),
    .address_alu_zero_ex(address_alu_zero_ex),
    .read_data_2_ex(read_data_2_ex),
    .inst_14_to_12_ex(inst_30_and_14_to_12_ex[2:0]),

    .branch_mem(branch_mem),
    .reg_write_mem(reg_write_mem),
    .mem_read_mem(mem_read_mem),
    .mem_write_mem(mem_write_mem),
    .mem_to_reg_mem(mem_to_reg_mem),
    .AuipcLui_mem(AuipcLui_mem),
    .inst_11_to_7_mem(inst_11_to_7_mem),
    .jump_alu_result_mem(jump_alu_result_mem),
    .address_alu_result_mem(address_alu_result_mem),
    .address_alu_zero_mem(address_alu_zero_mem),
    .read_data_2_mem(read_data_2_mem),
    .inst_14_to_12_mem(inst_14_to_12_mem)
);

assign ddata_w = read_data_2_mem;
assign daddr = address_alu_result_mem[11:2];
assign mem_write = mem_write_mem;
assign mem_read = mem_read_mem;

logic PCSrc;
assign PCSrc = branch_mem & ((inst_14_to_12_mem == 'b001 && !address_alu_zero_mem) || (inst_14_to_12_mem != 'b001 && address_alu_zero_mem));

logic [1:0] mem_to_reg_wb;
logic [DATA_SIZE-1:0] ddata_r_wb, address_alu_result_wb;
MEM_WB_REG mem_wb_reg(
    .clk(CLK),
    .clear(CLEAR),
    .mem_to_reg_mem(mem_to_reg_mem),
    .reg_write_mem(reg_write_mem),
    .ddata_r_mem(ddata_r),
    .address_alu_result_mem(address_alu_result_mem),
    .inst_11_to_7_mem(inst_11_to_7_mem),

    .mem_to_reg_wb(mem_to_reg_wb),
    .reg_write_wb(reg_write_wb),
    .ddata_r_wb(ddata_r_wb),
    .address_alu_result_wb(address_alu_result_wb),
    .inst_11_to_7_wb(inst_11_to_7_wb)
);

//Vamos a incluir un registro auxiliar para retrasar un ciclo la señal rd_wb, con el fin de poder tener otro tipo de data forwarding,
//porque nos hemos encontrado problemas porque se solapan y no coge el valor correcto, por eso vamos a aguantar un ciclo más la señal.
always_ff @( posedge CLK ) 
begin
    reg_write_wb_aux <= reg_write_wb;
    inst_11_to_7_wb_aux <= reg_write_wb_aux;
    data_mux_result_wire_aux <= data_mux_result_wire;
end

logic [DATA_SIZE-1:0] myInput_data_mux [3];
assign myInput_data_mux[0] = address_alu_result_wb;
assign myInput_data_mux[1] = ddata_r_wb;
assign myInput_data_mux[2] = {next_consecutive_pc_wire};
MUX #(.SIZE(DATA_SIZE), .INPUTS(3)) data_mux (
    .all_inputs(myInput_data_mux),
    .sel(mem_to_reg_wb),
    .result(data_mux_result_wire)
);

logic [ADDR_SIZE-1+2:0] myInput_pc_mux [2];
assign myInput_pc_mux[0] = next_consecutive_pc_wire;
assign myInput_pc_mux[1] = jump_alu_result_mem;
MUX #(.SIZE(ADDR_SIZE+2), .INPUTS(2)) pc_mux(
    .all_inputs(myInput_pc_mux),
    .sel(PCSrc),
    .result(next_pc_wire)
);
assign reg_write_data = data_mux_result_wire;
endmodule

`endif


