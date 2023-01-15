`ifndef SINGLE_CYCLE_GUARD
`define SINGLE_CYCLE_GUARD

`include "../Shared/MUX.sv"
`include "../Shared/ALU/ALU.sv"
`include "../Shared/ALU/operation_type.sv"
`include "../Shared/Control/ALU_CONTROL.sv"
`include "../Shared/Control/CONTROL.sv"
`include "../Shared/Control/IMMEDIATE_GENERATOR.sv"
`include "../Shared/Control/instruction_type.sv"

`include "./banco_registros/banco_registros_unregistered.sv"
`include "./memories/ram_unregistered.sv"
`include "./memories/rom_unregistered.sv"

module single_cycle
#(parameter SIZE = 32, parameter ADDR_WIDTH = 10)(
    input                       CLK,
    input                       RESET_N,
    input   [SIZE-1:0]          idata,
    output  [ADDR_WIDTH-1:0]    iaddr,
    output  [ADDR_WIDTH-1:0]    daddr,
    input   [SIZE-1:0]          ddata_r,
    output  [SIZE-1:0]          ddata_w,
    output                      d_rw,
    output  [SIZE-1:0]          reg_write_data,
    output                      reg_write_enable,
    output [4:0]                write_register
);

bit [ADDR_WIDTH-1+2:0] PC;
wire [ADDR_WIDTH-1+2:0] next_consecutive_pc_wire;

ALU #(.SIZE(ADDR_WIDTH+2)) pc_alu(
    .A(PC),
    .B(12'd4),
    .OPERATION(ADD),
    .RESULT(next_consecutive_pc_wire),
    .ZERO()
);

wire Branch, MemRed, MemWrite, ALUSrc, RegWrite;
wire [1:0] MemtoReg;
wire [1:0] AuipcLui_wire;
CONTROL control(
    .OPCODE(idata[6:0]),
    .BRANCH(Branch),
    .MEM_READ(MemRed),
    .MEM_TO_REG(MemtoReg),
    .MEM_WRITE(d_rw),
    .ALU_SRC(ALUSrc),
    .REG_WRITE(RegWrite),
    .AuipcLui(AuipcLui_wire)
);

wire [SIZE-1:0] data_mux_result_wire;
wire [SIZE-1:0] data_1_wire, data_2_wire;
banco_registros_unregistered #(.SIZE(SIZE)) registros(
    .CLK(CLK),
    .RESET_N(RESET_N),
    .read_reg1(idata[19:15]),
    .read_reg2(idata[24:20]),
    .write_reg(idata[11:7]),
    .writeData(data_mux_result_wire),
    .RegWrite(RegWrite),
    .Data1(data_1_wire),
    .Data2(data_2_wire)
);

assign ddata_w = data_2_wire;
assign reg_write_enable = RegWrite;
assign write_register = idata[11:7];
wire [SIZE-1:0] imm_wire;
//Como hay que trocear la instruccion a mano, solo funciona para 32 bits

IMMEDIATE_GENERATOR imm_gen(
    .inst(idata),
    .IMMEDIATE(imm_wire)
);

wire [SIZE-1:0] first_operand_wire;
wire [SIZE-1:0] myInput_alu_src_1_mux [3];
assign myInput_alu_src_1_mux[0] = PC;
assign myInput_alu_src_1_mux[1] = 32'b0;
assign myInput_alu_src_1_mux[2] = data_1_wire;

MUX #(.SIZE(32), .INPUTS(3)) alu_src_1_mux (
    .all_inputs(myInput_alu_src_1_mux),
    .sel(AuipcLui_wire),
    .result(first_operand_wire)
);

wire [SIZE-1:0] second_operand_wire;
wire [SIZE-1:0] myInput_alu_src_2_mux [2];
assign myInput_alu_src_2_mux[0] = data_2_wire;
assign myInput_alu_src_2_mux[1] = imm_wire;

MUX #(.SIZE(SIZE), .INPUTS(2)) alu_src_2_mux (
    .all_inputs(myInput_alu_src_2_mux),
    .sel(ALUSrc),
    .result(second_operand_wire)
);

wire [3:0] ALUSelection_wire;
ALU_CONTROL alu_control(
    .OPCODE(idata[6:0]),
    .funct3(idata[14:12]),
    .bit30(idata[30]),
    .ALUSelection(ALUSelection_wire)
);

wire address_alu_zero;
wire [SIZE-1:0] address_alu_result;
ALU #(.SIZE(SIZE)) address_alu(
    .A(first_operand_wire),
    .B(second_operand_wire),
    .OPERATION(ALUSelection_wire),
    .RESULT(address_alu_result),
    .ZERO(address_alu_zero)
);

assign daddr = {2'b0, address_alu_result[31:2]};


wire [SIZE-1:0] myInput_data_mux [3];
assign myInput_data_mux[0] = address_alu_result;
assign myInput_data_mux[1] = ddata_r;
assign myInput_data_mux[2] = {20'b0, next_consecutive_pc_wire[11:0]};

MUX #(.SIZE(SIZE), .INPUTS(3)) data_mux (
    .all_inputs(myInput_data_mux),
    .sel(MemtoReg),
    .result(data_mux_result_wire)
);

wire [ADDR_WIDTH+2-1:0] branch_target_wire;
ALU #(.SIZE(ADDR_WIDTH+2)) jump_alu(
    .A(PC),
    .B(imm_wire[11:0]),
    .OPERATION(ADD),
    .RESULT(branch_target_wire),
    .ZERO()
);

wire PCSrc;
assign PCSrc = Branch & ((idata[ 14:12] == 000 && address_alu_zero) || (idata[14:12] != 000 && !address_alu_zero));
wire [ADDR_WIDTH+2-1:0] next_pc_wire;

wire [ADDR_WIDTH+2-1:0] myInput_pc_mux [2];
assign myInput_pc_mux[0] = next_consecutive_pc_wire;
assign myInput_pc_mux[1] = branch_target_wire;

MUX #(.SIZE(ADDR_WIDTH+2), .INPUTS(2)) pc_mux(
    .all_inputs(myInput_pc_mux),
    .sel(PCSrc),
    .result(next_pc_wire)
);


always @(posedge CLK or negedge RESET_N) begin
    if(RESET_N == 0) begin
        PC <= 0;
    end else begin
        PC <= next_pc_wire;
    end
end
assign iaddr = PC[11:2];

assign reg_write_data = data_mux_result_wire; //para el golden

logic [6:0] opcode;
logic [2:0] funct3;
logic [6:0] funct7;
logic [4:0] rs1;
logic [4:0] rs2;
logic [4:0] rd;
logic [31:0] immediate;



endmodule

`endif //SINGLE_CYCLE_GUARD