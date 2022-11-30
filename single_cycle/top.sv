module top(
    input CLK, 
    input RESET_N
);
localparam SIZE = 32, ADDR_WIDTH = 10;

bit [SIZE-1:0] PC;
wire [SIZE1:0] next_consecutive_pc_wire;

ALU #(.SIZE(SIZE)) pc_alu(
    .A(PC),
    .B('d4),
    .OPERATION(ADD),
    .RESULT(next_consecutive_pc_wire),
);

wire [SIZE-1:0] instruction_wire;
ROM #(.data_width(SIZE),.addr_width(ADDR_WIDTH)) instruction_memory (
    .ADDR_R(PC),
    .Q_R(instruction_wire)
);

wire Branch, MemRed, MemtoReg, ALUOp, MemWrite, ALUSrc, RegWrite;
CONTROL control(
    .INSTRUCTION_FORMAT(instruction_wire[6_0]),
    .BRANCH(Branch),
    .MEM_READ(MemRed),
    .MEM_TO_REG(MemtoReg),
    .ALU_OP(ALUOp),
    .MEM_WRITE(MemWrite),
    .ALU_SRC(ALUSrc),
    .REG_WRITE(RegWrite)
);

wire [SIE-1:0] data_1_wire, data_2_wire;
BANCO_REGISTROS #(.SIZE(SIZE)) registros(
    .CLK(CLK),
    .RESET_N(RESET_N),
    .reg1r(instruction_wire[19:15]),
    .reg2r(instruction_wire[24:20]),
    .regW(instruction_wire[11:7]),
    .writeData(data_mux_result_wire),
    .RegWrite(RegWrite),
    .Data1(data_1_wire),
    .Data2(data_2_wire)
);

wire [SIZE-1:0] imm_wire;
//Como hay que trocear la instruccion a mano, solo funciona para 32 bits
IMMEDIATE_GENERATOR imm_gen(
    .INSTRUCTION(instruction_wire),
    .IMMEDIATE(imm_wire)
);

wire [SIZE-1:0] second_operand_wire;
MUX #(.SIZE(SIZE), .INPUTS(2)) alu_src_mux (
    .all_inputs({data_2_wire,imm_wire}),
    .sel(ALUSrc),
    .result(second_operand_wire)
);

wire [SIZE-1:0] address_alu_operation_wire;
ALU_CONTROL alu_control(
    .(),
    .ALU_OPERATION(ALUOp),
    .ADDRESS_ALU_OPERATION(address_alu_operation_wire)
);

wire [SIZE-1:0] alu_operation_wire;
wire address_alu_zero;
ALU #(.SIZE(SIZE)) address_alu(
    .A(data_1_wire),
    .B(second_operand_wire),
    .OPERATION(address_alu_operation_wire),
    .RESULT(alu_address_wire),
    .ZERO(address_alu_zero)
);

wire [SIZE-1:0] read_data_wire;
RAM #(.data_width(SIZE), .addr_width(ADDR_WIDTH)) data_memory (
    .CLK(CLK),
    .ENABLE_W(MemWrite),
    .ADDR_R(alu_address_wire),
    .ADDR_W(alu_address_wire),
    .Q_W(data_2_wire),
    .Q_R(read_data_wire)

);

wire [SIZE-1:0] data_mux_result_wire;
MUX #(.SIZE(SIZE), .INPUTS(2)) data_mux (
    .all_inputs({alu_address_wire,read_data_wire})
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
MUX #(.SIZE(SIZE), .INPUTS(INPUTS)) pc_mux(
    .all_inputs({next_consecutive_pc_wire,branch_target_wire})
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
endmodule