`include "../ALU/operation_type.sv"

module top
#(parameter SIZE = 32, parameter ADDR_WIDTH = 10)(
    input CLK, 
    input RESET_N,
    input  [SIZE-1:0] Q_ROM,
    output  [ADDR_WIDTH-1:0] ADDR_ROM,
    output  [ADDR_WIDTH-1:0] ADDR_RAM,
    input  [SIZE-1:0] Q_RAM,
    output  [SIZE-1:0] Q_W,
    output ENABLE_W
    
);


bit [ADDR_WIDTH-1:0] PC;
wire [SIZE-1:0] next_consecutive_pc_wire;

ALU #(.SIZE(ADDR_WIDTH)) pc_alu(
    .A(PC),
    //FIXME: sumamos 1 o 4
    .B('d1),
    .OPERATION(ADD),
    .RESULT(next_consecutive_pc_wire),
    .ZERO()
);

wire Branch, MemRed, MemtoReg, MemWrite, ALUSrc, RegWrite;
wire [1:0] AuipcLui_wire;
CONTROL control(
    .OPCODE(Q_ROM[6:0]),
    .BRANCH(Branch),
    .MEM_READ(MemRed),
    .MEM_TO_REG(MemtoReg),
    .MEM_WRITE(ENABLE_W),
    .ALU_SRC(ALUSrc),
    .REG_WRITE(RegWrite),
    .AuipcLui(AuipcLui_wire)
);

wire [SIZE-1:0] data_mux_result_wire;
wire [SIZE-1:0] data_1_wire, data_2_wire;
BANCO_REGISTROS #(.SIZE(SIZE)) registros(
    .CLK(CLK),
    .RESET_N(RESET_N),
    .read_reg1(Q_ROM[19:15]),
    .read_reg2(Q_ROM[24:20]),
    .write_reg(Q_ROM[11:7]),
    .writeData(data_mux_result_wire),
    .RegWrite(RegWrite),
    .Data1(data_1_wire),
    .Data2(data_2_wire)
);
assign Q_W = data_2_wire;
wire [SIZE-1:0] imm_wire;
//Como hay que trocear la instruccion a mano, solo funciona para 32 bits

IMMEDIATE_GENERATOR imm_gen(
    .inst(Q_ROM),
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
    .OPCODE(Q_ROM[6:0]),
    .funct3(Q_ROM[14:12]),
    .bit30(Q_ROM[30]),
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

assign ADDR_RAM = address_alu_result;

/*wire [SIZE-1:0] read_data_wire;
RAM #(.data_width(SIZE), .addr_width(ADDR_WIDTH)) data_memory (
    .CLK(CLK),
    .ENABLE_W(MemWrite),
    .ADDR_R(alu_address_wire),
    .ADDR_W(alu_address_wire),
    .Q_W(data_2_wire),
    .Q_R(read_data_wire)

);*/

wire [SIZE-1:0] myInput_data_mux [2];
assign myInput_data_mux[0] = address_alu_result;
assign myInput_data_mux[1] = Q_RAM;

MUX #(.SIZE(SIZE), .INPUTS(2)) data_mux (
    .all_inputs(myInput_data_mux),
    .sel(MemtoReg),
    .result(data_mux_result_wire)
);

wire [SIZE-1:0] branch_target_wire;
ALU #(.SIZE(SIZE)) jump_alu(
    .A(PC),
    .B(imm_wire),
    .OPERATION(ADD),
    .RESULT(branch_target_wire),
    .ZERO()
);

wire PCSrc;
assign PCSrc = Branch & address_alu_zero;
wire [ADDR_WIDTH-1:0] next_pc_wire;

wire [SIZE-1:0] myInput_pc_mux [2];
assign myInput_pc_mux[0] = next_consecutive_pc_wire;
assign myInput_pc_mux[1] = branch_target_wire;

MUX #(.SIZE(SIZE), .INPUTS(2)) pc_mux(
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
assign ADDR_ROM = PC; 
endmodule