`include "../ALU/operation_type.sv"

module top
#(parameter SIZE = 32, parameter ADDR_WIDTH = 10)(
    input CLK, 
    input RESET_N,
    input  [(SIZE-1):0]Q_ROM,
    output  [(ADDR_WIDTH-1):0] ADDR_ROM,
    output  [(ADDR_WIDTH-1):0] ADDR_RAM,
    input  [(SIZE-1):0] Q_RAM,
    output  [(SIZE-1):0] Q_W,
    output ENABLE_W
    
);


bit [ADDR_WIDTH-1:0] PC;
wire [SIZE-1:0] next_consecutive_pc_wire;

ALU #(.SIZE(SIZE)) pc_alu(
    .A(PC),
    .B('d4),
    .OPERATION(ADD),
    .RESULT(next_consecutive_pc_wire)
);

/*wire [SIZE-1:0] instruction_wire;
ROM #(.data_width(SIZE),.addr_width(ADDR_WIDTH)) instruction_memory (
    .ADDR_R(PC),
    .Q_R(instruction_wire)
);*/

wire Branch, MemRed, MemtoReg, ALUOp, MemWrite, ALUSrc, RegWrite;
wire [1:0] AuipcLui_wire;
CONTROL control(
    .INSTRUCTION_FORMAT(Q_ROM[6:0]),
    .BRANCH(Branch),
    .MEM_READ(MemRed),
    .MEM_TO_REG(MemtoReg),
    .ALU_OP(ALUOp),
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
    .reg1r(Q_ROM[19:15]),
    .reg2r(Q_ROM[24:20]),
    .regW(Q_ROM[11:7]),
    .writeData(data_mux_result_wire),
    .RegWrite(RegWrite),
    .Data1(data_1_wire),
    .Data2(data_2_wire)
);
assign data_2_wire = Q_W;
wire [SIZE-1:0] imm_wire;
//Como hay que trocear la instruccion a mano, solo funciona para 32 bits
IMMEDIATE_GENERATOR imm_gen(
    .INSTRUCTION(Q_ROM),
    .IMMEDIATE(imm_wire)
);

wire [SIZE-1:0] first_operand_wire;
MUX #(.SIZE(32), .INPUTS(3)) alu_src_1_mux (
    .all_inputs({PC, 32'b0, data_1_wire}),
    .sel(AuipcLui_wire),
    .result(first_operand_wire)
);

wire [SIZE-1:0] second_operand_wire;
MUX #(.SIZE(SIZE), .INPUTS(2)) alu_src_mux (
    .all_inputs({data_2_wire, imm_wire}),
    .sel(ALUSrc),
    .result(second_operand_wire)
);

wire [3:0] ALUSelection_wire;
ALU_CONTROL alu_control(
    .funct3(Q_ROM[14:12]),
    .bit30(Q_ROM[30]),
    .ALUOp(ALUOp),
    .ALUSelection(ALUSelection_wire)
);

wire [SIZE-1:0] alu_operation_wire;
wire address_alu_zero;
ALU #(.SIZE(SIZE)) address_alu(
    .A(first_operand_wire),
    .B(second_operand_wire),
    .OPERATION(ALUSelection_wire),
    .RESULT(ADDR_RAM),
    .ZERO(address_alu_zero)
);

/*wire [SIZE-1:0] read_data_wire;
RAM #(.data_width(SIZE), .addr_width(ADDR_WIDTH)) data_memory (
    .CLK(CLK),
    .ENABLE_W(MemWrite),
    .ADDR_R(alu_address_wire),
    .ADDR_W(alu_address_wire),
    .Q_W(data_2_wire),
    .Q_R(read_data_wire)

);*/


MUX #(.SIZE(SIZE), .INPUTS(2)) data_mux (
    .all_inputs({ADDR_RAM, Q_RAM}),
    .sel(MemtoReg),
    .result(data_mux_result_wire)
);

wire [SIZE-1:0] branch_target_wire;
ALU #(.SIZE(SIZE)) jump_alu(
    .A(PC),
    .B(imm_wire),
    .OPERATION(ADD),
    .RESULT(branch_target_wire)
);

wire PCSrc;
assign PCSrc = Branch & address_alu_zero;
wire [SIZE-1:0] next_pc_wire;
MUX #(.SIZE(SIZE), .INPUTS(2)) pc_mux(
    .all_inputs({next_consecutive_pc_wire,branch_target_wire}),
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