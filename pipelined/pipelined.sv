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

`include "./risk_detection/hazard_detection.sv"
`include "./risk_detection/jump_predictor.sv"
`include "././risk_detection/data_forwarding.sv"

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

wire [ADDR_SIZE + 2 - 1:0] next_pc_wire;
wire PCWrite;
logic [ADDR_SIZE + 2 - 1:0] PC;

initial begin
    PC = 0;
end

wire do_jump_wire;

wire [ADDR_SIZE + 2 - 1:0] final_pc;
assign final_pc = (PCWrite) ? next_pc_wire : PC;
always @(posedge CLK or negedge RESET_N) begin
    if(RESET_N == 0) begin
        PC <= 0;
    end else begin
        PC <= final_pc;
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

wire [ADDR_SIZE + 2 - 1: 0] predictor_jump_pc_wire;

wire [9:0] iaddr_mux_control[2];
assign iaddr_mux_control[0] = PC[11:2];
assign iaddr_mux_control[1] = predictor_jump_pc_wire[11:2];
MUX #(.SIZE(ADDR_SIZE), .INPUTS(2)) iaddr_mux(
    .all_inputs(iaddr_mux_control),
    .sel(do_jump_wire),
    .result(iaddr)
);

wire branch_ex, reg_write_ex, mem_read_ex, mem_write_ex, alu_src_ex;
wire [DATA_SIZE-1:0] inst_id;
wire if_id_enable;
wire control_mux_sel;

wire [1:0] mem_to_reg_ex, AuipcLui_ex;
wire [ADDR_SIZE-1+2:0] pc_ex;
wire [DATA_SIZE-1:0] read_data_1_ex, read_data_2_ex, immediate_ex;
wire [3:0] inst_30_and_14_to_12_ex;
wire [4:0] inst_11_to_7_ex;
wire [6:0] inst_6_to_0_ex;
wire [8:0] salida_mux_control;
wire [8:0] input_mux_control[2];
wire [4:0] inst_11_to_7_mem;
wire reg_write_mem, mem_read_mem;

hazard_detection #(.SIZE(DATA_SIZE)) hazard_detection(
    .id_rs1(inst_id[19:15]),
    .id_rs2(inst_id[24:20]),
    .mem_read_mem(mem_read_mem),
    .rd_register_mem(inst_11_to_7_mem),
    .reg_write_mem(reg_write_mem),
    .PCWrite(PCWrite),
    .if_id_enable(if_id_enable),
    .enable_nop_mux(control_mux_sel)
    );

wire [ADDR_SIZE-1+2:0] pc_id;
IF_ID_REG #(.DATA_SIZE(DATA_SIZE), .ADDR_SIZE(ADDR_SIZE)) if_id_reg(
    .clk(CLK),
    .enable(if_id_enable),
    .pc_if(PC),
    .inst_if(idata),
    .pc_id(pc_id),
    .inst_id(inst_id)
);

wire branch_id, reg_write_id, mem_read_id, mem_write_id, alu_src_id;
wire [1:0] mem_to_reg_id;
wire [1:0] AuipcLui_id;

//wire [6:0] control_delayed = CLEAR ? 7'h13 : inst_id[6:0];
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

wire force_nop_wire;
assign input_mux_control[0] = {branch_id,reg_write_id,mem_read_id,mem_write_id,alu_src_id,mem_to_reg_id,AuipcLui_id};
assign input_mux_control[1] = 9'b0;
MUX #(.SIZE(9), .INPUTS(2)) control_mux(
    .all_inputs(input_mux_control),
    .sel(control_mux_sel || force_nop_wire), //enable mux que sale del hazard
    .result(salida_mux_control)
);

wire [DATA_SIZE-1:0] read_data_1_id, read_data_2_id;
wire [DATA_SIZE-1:0] data_mux_result_wire;
wire reg_write_wb;
wire [4:0] inst_11_to_7_wb;

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

wire branch_id_mux,reg_write_id_mux,mem_read_id_mux,mem_write_id_mux,alu_src_id_mux;
wire [1:0]  mem_to_reg_id_mux, AuipcLui_id_mux;
assign {
    branch_id_mux,
    reg_write_id_mux,
    mem_read_id_mux,
    mem_write_id_mux,
    alu_src_id_mux,
    mem_to_reg_id_mux,
    AuipcLui_id_mux
} = salida_mux_control;

wire [4:0] inst_19_to_15_ex;
wire [4:0] inst_24_to_20_ex;
ID_EX_REG id_ex_reg(
    .clk(CLK),
    .clear(CLEAR),
    .branch_id(branch_id_mux),
    .reg_write_id(reg_write_id_mux),
    .mem_read_id(mem_read_id_mux),
    .mem_write_id(mem_write_id_mux),
    .alu_src_id(alu_src_id_mux),
    .mem_to_reg_id(mem_to_reg_id_mux),
    .AuipcLui_id(AuipcLui_id_mux),
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

wire [1:0] forwardA, forwardB;
wire [DATA_SIZE-1:0] second_operand_wire;
wire [DATA_SIZE-1:0] myInput_alu_src_2_mux[2];

logic [4:0] inst_11_to_7_wb_aux;
logic reg_write_wb_aux;
logic [DATA_SIZE-1:0] data_mux_result_wire_aux;

initial begin
    reg_write_wb_aux = 0;
    inst_11_to_7_wb_aux = 0;
    data_mux_result_wire_aux = 0;
end


wire [3:0] ALUSelection_wire;
ALU_CONTROL alu_control(
    .OPCODE(inst_6_to_0_ex),
    .funct3(inst_30_and_14_to_12_ex[2:0]),
    .bit30(inst_30_and_14_to_12_ex[3]),
    .ALUSelection(ALUSelection_wire)
);
wire [DATA_SIZE-1:0] address_alu_result_mem;
wire [DATA_SIZE-1:0] rs1_mux_input [4];
wire [DATA_SIZE-1:0] rs1_mux_result;
assign rs1_mux_input [0] = read_data_1_ex;
assign rs1_mux_input [2] =  address_alu_result_mem;
assign rs1_mux_input [1] = data_mux_result_wire;
assign rs1_mux_input [3] = data_mux_result_wire_aux;
MUX #(.SIZE(DATA_SIZE), .INPUTS(4)) rs1_mux(
    .all_inputs(rs1_mux_input),
    .sel(forwardA),
    .result(rs1_mux_result)
);

wire [DATA_SIZE-1:0] rs2_mux_input [4];
wire [DATA_SIZE-1:0] rs2_mux_result;
assign rs2_mux_input [0] = read_data_2_ex;
assign rs2_mux_input [2] =  address_alu_result_mem;
assign rs2_mux_input [1] = data_mux_result_wire;
assign rs2_mux_input [3] = data_mux_result_wire_aux;
MUX #(.SIZE(DATA_SIZE), .INPUTS(4)) rs2_mux(
    .all_inputs(rs2_mux_input),
    .sel(forwardB),
    .result(rs2_mux_result)
);

assign myInput_alu_src_2_mux[0] = rs2_mux_result;
assign myInput_alu_src_2_mux[1] = immediate_ex;
MUX #(.SIZE(DATA_SIZE), .INPUTS(2)) alu_src_2_mux (
    .all_inputs(myInput_alu_src_2_mux),
    .sel(alu_src_ex),
    .result(second_operand_wire)
);

wire [DATA_SIZE-1:0] address_alu_result_ex;
wire address_alu_zero_ex;
ALU #(.SIZE(DATA_SIZE)) address_alu(
    .A(rs1_mux_result),
    .B(second_operand_wire),
    .OPERATION(ALUSelection_wire),
    .RESULT(address_alu_result_ex),
    .ZERO(address_alu_zero_ex)
);



data_forwarding #(.SIZE(DATA_SIZE)) data_forwarding(
    .reg_write_mem(reg_write_mem), 
    .reg_write_ex(reg_write_ex),
    .reg_write_wb(reg_write_wb),
    .reg_write_wb_aux(reg_write_wb_aux),
    .rd_mem(inst_11_to_7_mem),
    .rd_wb(inst_11_to_7_wb),
    .rd_wb_aux(inst_11_to_7_wb_aux),
    .rs1_ex(inst_19_to_15_ex),
    .rs2_ex(inst_24_to_20_ex),
    .opcode_ex(inst_6_to_0_ex),
    .forwardA(forwardA),
    .forwardB(forwardB)
);
logic branch_mem, mem_write_mem;
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
    .address_alu_result_ex(address_alu_result_ex),
    .address_alu_zero_ex(address_alu_zero_ex),
    .read_data_2_ex(second_operand_wire),
    .inst_14_to_12_ex(inst_30_and_14_to_12_ex[2:0]),

    .branch_mem(branch_mem),
    .reg_write_mem(reg_write_mem),
    .mem_read_mem(mem_read_mem),
    .mem_write_mem(mem_write_mem),
    .mem_to_reg_mem(mem_to_reg_mem),
    .AuipcLui_mem(AuipcLui_mem),
    .inst_11_to_7_mem(inst_11_to_7_mem),
    .address_alu_result_mem(address_alu_result_mem),
    .address_alu_zero_mem(address_alu_zero_mem),
    .read_data_2_mem(read_data_2_mem),
    .inst_14_to_12_mem(inst_14_to_12_mem)
);

assign ddata_w = read_data_2_mem;
assign daddr = address_alu_result_mem[11:2];
assign mem_write = mem_write_mem;
assign mem_read = mem_read_mem;

wire should_have_jumped_wire;
assign should_have_jumped_wire = branch_ex && ((inst_30_and_14_to_12_ex[2:0] == 'b001 && !address_alu_zero_ex) || (inst_30_and_14_to_12_ex[2:0] != 'b001 && address_alu_zero_ex));

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
always @( posedge CLK ) 
begin
    reg_write_wb_aux <= reg_write_wb;
    inst_11_to_7_wb_aux <= inst_11_to_7_wb;
    data_mux_result_wire_aux <= data_mux_result_wire;
end

wire [DATA_SIZE-1:0] myInput_data_mux [3];
assign myInput_data_mux[0] = address_alu_result_wb;
assign myInput_data_mux[1] = ddata_r_wb;
assign myInput_data_mux[2] = {next_consecutive_pc_wire};
MUX #(.SIZE(DATA_SIZE), .INPUTS(3)) data_mux (
    .all_inputs(myInput_data_mux),
    .sel(mem_to_reg_wb),
    .result(data_mux_result_wire)
);


assign reg_write_data = data_mux_result_wire; //para el golden

wire [ADDR_SIZE - 1 + 2:0] jump_alu_result;
ALU #(.SIZE(ADDR_SIZE + 2)) jump_alu(
    .A(pc_id),
    .B(immediate_id[11:0]),
    .OPERATION(ADD),
    .RESULT(jump_alu_result),
    .ZERO()
);

jump_predictor #(.PC_SIZE(ADDR_SIZE + 2)) jump_predictor(
    .CLK(CLK),
    .RESET_N(RESET_N),
    .opcode(inst_id[6:0]),
    .current_pc(pc_id),
    .next_consecutive_pc(next_consecutive_pc_wire),
    .jump_pc(jump_alu_result),
    .should_have_jumped(should_have_jumped_wire),
    .do_jump(do_jump_wire),
    .predictor_jump_pc(predictor_jump_pc_wire),
    .force_nop(force_nop_wire)
);

wire [ADDR_SIZE-1+2:0] myInput_pc_mux[2];
assign myInput_pc_mux[0] = next_consecutive_pc_wire;
assign myInput_pc_mux[1] = predictor_jump_pc_wire + 4;
MUX #(.SIZE(ADDR_SIZE + 2), .INPUTS(2)) pc_mux(
    .all_inputs(myInput_pc_mux),
    .sel(do_jump_wire),
    .result(next_pc_wire)
);
assign reg_write_data = data_mux_result_wire;
endmodule

`endif


