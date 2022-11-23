module top(
    input CLK, 
    input RESET_N
);
localparam SIZE = 32, ADDR_WIDTH = 10;

bit [SIZE-1:0] PC;
wire [SIZE1:0] next_pc_wire;

ALU #(.SIZE(SIZE)) pc_alu(
    .A(PC),
    .B('d4),
    .OPERATION(ADD),
    .RESULT(next_pc_wire),
);

wire [SIZE-1:0] instruction_wire;
ROM #(.data_width(SIZE),.addr_width(ADDR_WIDTH)) instruction_memory (
    .ADDR_R(PC),
    .Q_R(instruction_wire)
);

wire [SIE-1:0] data_1_wire, data_2_wire;
BANCO_REGISTROS #(.SIZE(SIZE)) registros(
    .CLK(CLK),
    .RESET_N(RESET_N),
    .reg1r(instruction_wire),
    .reg2r(instruction_wire),
    .regW(),
    .writeData(),
    .RegWrite(),
    .Data1(data_1_wire),
    .Data2(data_2_wire)
);

wire [SIZE-1:0] imm_wire;
//Como hay que trocear la instruccion a mano, solo funciona para 32 bits
IMMEDIATE_GENERATOR imm_gen(
    .INSTRUCTION(instruction_wire),
    .IMMEDIATE(imm_wire)
);

wire ALUSrc;
wire [SIZE-1:0] second_operand_wire;
MUX #(.SIZE(SIZE)) alu_src_mux (
    .A(data_2_wire),
    .B(imm_wire),
    .SEL(ALUSrc),
    .RESULT(second_operand_wire)
);

RAM #(.data_width(SIZE), .addr_width(ADDR_WIDTH)) data_memory (
    .CLK(CLK),
    .ADDR_W
);

wire [SIZE-1:0] branch_target_wire;
ALU #(.SIZE(SIZE)) jump_alu(
    .A(PC),
    .B(imm_wire),
    .OPERATION(ADD),
    .RESULT(branch_target_wire)
);

wire [SIZE-1:0] alu_operation_wire;
wire [SIZE1:0] address_wire;
wire address_alu_zero;
ALU #(.SIZE(SIZE)) address_alu(
    .A(data_1_wire),
    .B(data_2_wire),
    .OPERATION(alu_operation_wire),
    .RESULT(address_wire),
    .ZERO(address_alu_zero)
);

always @(posedge CLK or negedge RESET_N) begin
    if(RESET_N == 0) begin
        PC <= 0;
    end else begin
        PC <= next_pc_wire;
    end
end