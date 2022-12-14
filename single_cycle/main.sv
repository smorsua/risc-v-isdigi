`ifndef MAIN_GUARD
`define MAIN_GUARD

`include "../ALU/operation_type.sv"
`include "instruction_type.sv"
module main
#(parameter SIZE = 32, parameter ADDR_WIDTH = 10)(
    input CLK,
    input RESET_N,
    input  [SIZE-1:0] idata,
    output  [ADDR_WIDTH-1:0] iaddr,
    output  [ADDR_WIDTH-1:0] daddr,
    input  [SIZE-1:0] ddata_r,
    output  [SIZE-1:0] ddata_w,
    output d_rw
);

bit [ADDR_WIDTH-1:0] PC_aux;
always_ff @(posedge CLK or negedge RESET_N) begin
    if(RESET_N == 0) begin
        PC_aux <= 0;
    end else begin
        PC_aux <= next_pc_wire;
    end
end

always_ff @( posedge CLK ) begin : 
    PC <= PC_aux;    
end

assign iaddr = {2'b0, PC[9:2]};


bit [ADDR_WIDTH-1:0] PC;
wire [ADDR_WIDTH-1:0] next_consecutive_pc_wire;

ALU #(.SIZE(ADDR_WIDTH)) pc_alu(
    .A(PC),
    .B(10'd4),
    .OPERATION(ADD),
    .RESULT(next_consecutive_pc_wire),
    .ZERO()
);


wire Branch, MemRed, MemWrite, ALUSrc, RegWrite;
wire [1:0] MemtoReg;
wire [1:0] AuipcLui_wire;
CONTROL control(

    .WB(MemtoReg),
    .M(d_rw),
    .EX(ALUSrc), //SALEN alusCR aluoP

   /* .OPCODE(idata[6:0]),
    .BRANCH(Branch),
    .MEM_READ(MemRed),
    .MEM_TO_REG(MemtoReg),
    .MEM_WRITE(d_rw),
    .ALU_SRC(ALUSrc),
    .REG_WRITE(RegWrite),
    .AuipcLui(AuipcLui_wire)*/
);

wire [SIZE-1:0] data_mux_result_wire;
wire [SIZE-1:0] data_1_wire, data_2_wire;
BANCO_REGISTROS #(.SIZE(SIZE)) registros(
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
assign myInput_data_mux[2] = {22'b0, next_consecutive_pc_wire[9:0]};

MUX #(.SIZE(SIZE), .INPUTS(3)) data_mux (
    .all_inputs(myInput_data_mux),
    .sel(MemtoReg),
    .result(data_mux_result_wire)
);

wire [ADDR_WIDTH-1:0] branch_target_wire;
ALU #(.SIZE(ADDR_WIDTH)) jump_alu(
    .A(PC),
    .B(imm_wire),
    .OPERATION(ADD),
    .RESULT(branch_target_wire),
    .ZERO()
);

wire PCSrc;
assign PCSrc = Branch & ((idata[14:12] == 001 && !address_alu_zero) || (idata[14:12] != 001 && address_alu_zero));
wire [ADDR_WIDTH-1:0] next_pc_wire;

wire [ADDR_WIDTH-1:0] myInput_pc_mux [2];
assign myInput_pc_mux[0] = next_consecutive_pc_wire;
assign myInput_pc_mux[1] = branch_target_wire;

MUX #(.SIZE(ADDR_WIDTH), .INPUTS(2)) pc_mux(
    .all_inputs(myInput_pc_mux),
    .sel(PCSrc),
    .result(next_pc_wire)
);





logic [6:0] opcode;
logic [2:0] funct3;
logic [6:0] funct7;
logic [4:0] rs1;
logic [4:0] rs2;
logic [4:0] rd;
logic [31:0] immediate;

always @(posedge CLK) begin
    opcode = idata[6:0];
    casex(opcode)
    R_FORMAT: begin
        rd = idata[11:7];
        funct3 = idata[14:12];
        rs1 = idata[19:15];
        rs2 = idata[24:20];
        funct7 = idata[31:25];
        casex(funct3)
        3'b000: begin
            case(funct7)
            /*ADD*/ 7'b0000000: assert(data_mux_result_wire == data_1_wire + data_2_wire);
            /*SUB*/ 7'b0100000: assert(data_mux_result_wire == data_1_wire - data_2_wire);
            default: $error("Incorrect funct7");
            endcase
        end
        /*SLL*/  3'b001: assert(data_mux_result_wire == (data_1_wire << data_2_wire));
        /*SLT*/  3'b010: assert(data_mux_result_wire == (!(signed'(data_1_wire) < signed'(data_2_wire))));
        /*SLTU*/ 3'b011: assert(data_mux_result_wire == (!(data_1_wire < data_2_wire)));
        /*XOR*/  3'b100: assert(data_mux_result_wire == (data_1_wire ^ data_2_wire));
        3'b101: begin
            case(funct7)
            /*SRL*/ 7'b0000000: assert(data_mux_result_wire == (data_1_wire >> data_2_wire));
            /*SRA*/ 7'b0100000: assert(data_mux_result_wire == (data_1_wire >>> data_2_wire));
            default: $error("Incorrect funct 7");
            endcase
        end
        /*OR*/ 3'b110: assert(data_mux_result_wire == (data_1_wire | data_2_wire));
        /*AND*/ 3'b111: assert(data_mux_result_wire == (data_1_wire & data_2_wire));
        default: $error("Incorrect funct3");
        endcase
    end
    I_FORMAT: begin
        funct3 = idata[14:12];
        rs1 = idata[19:15];
        rd = idata[11:7];
        immediate = { {21{idata[31]}}, idata[30:20] };

        case(opcode)
        7'b0000011: begin //memory operations
            /*LW*/ assert(data_mux_result_wire == ddata_r) ;

        end
        7'b0010011: begin //arithmetic operations
            case(funct3)
            /*ADDI*/ 3'b000: assert(data_mux_result_wire == (data_1_wire + immediate));
            /*SLLI*/ 3'b001: assert(data_mux_result_wire == (data_1_wire << immediate));
            /*SLTIU*/3'b011: assert(data_mux_result_wire == (!(data_1_wire < immediate)));
            /*XORI*/ 3'b100: assert(data_mux_result_wire == (data_1_wire ^ immediate));
            /*SLTI*/ 3'b010: assert(data_mux_result_wire == (!(signed'(data_1_wire) < signed'(immediate))));
            3'b101: begin
                case(immediate[11:6])
                /*SRLI*/ 7'b0000000: assert(data_mux_result_wire == (data_1_wire >> immediate[5:0]));
                /*SRAI*/ 7'b0100000: assert(data_mux_result_wire == (data_1_wire >>> immediate[5:0]));
                endcase
            end
            /*ORI*/ 3'b110: assert(data_mux_result_wire == (data_1_wire | immediate));
            /*ANDI*/3'b111: assert(data_mux_result_wire == (data_1_wire & immediate));
            default: $error("Invalid funct3");
            endcase
        end
        default: $error("Invalid opcode");
        endcase
    end
    U_FORMAT: begin
        rd = idata[11:7];
        immediate = { idata[31:12], 12'b0 };
        case(opcode)
        /*AUIPC*/ 7'b0010111: assert(data_mux_result_wire == PC + immediate);
        /*LUI*/ 7'b0110111: assert(data_mux_result_wire == immediate);
        default: $error("invalid opcode");
        endcase
    end
    S_FORMAT: begin
        immediate = { {21{idata[31]}}, idata[30:25], idata[11:7]};
        /*SW*/ assert(address_alu_result == data_1_wire + immediate);
    end
    B_FORMAT: begin
        immediate = { {21{idata[31]}}, idata[7], idata[30:25], idata[11:8], 1'b0};
        
    end

    default: $error("Invalid instruction format");
    endcase
end

// assert property (@(posedge CLK) address_alu_zero == '1 && idata[6:0] == 'b1100011 |-> (branch_target_wire == (immediate + PC)) ) else $fatal("No realiza correctamente el salto condicional");

endmodule

`endif //MAIN_GUARD