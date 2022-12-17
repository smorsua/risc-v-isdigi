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
    output MemWrite, MemRead
);

wire [ADDR_WIDTH-1:0] next_pc_wire;

bit [ADDR_WIDTH-1:0] PC_aux;
bit [ADDR_WIDTH-1:0] PC; 

always_ff @(posedge CLK or negedge RESET_N) begin
    if(RESET_N == 0) begin
        PC_aux <= 0;
    end else begin
        PC_aux <= next_pc_wire;
    end
end

always_ff @( posedge CLK ) begin 
    PC <= PC_aux;    
end
assign iaddr = {2'b0, PC[9:2]};


wire [ADDR_WIDTH-1:0] next_consecutive_pc_wire;

ALU #(.SIZE(ADDR_WIDTH)) pc_alu(
    .A(PC_aux),
    .B(10'd4),
    .OPERATION(ADD),
    .RESULT(next_consecutive_pc_wire),  
    .ZERO()
);

wire Branch, ALUSrc, RegWrite;
wire [1:0] MemtoReg;
wire [1:0] AuipcLui_wire;
CONTROL control(
    .OPCODE(idata[6:0]), 
    .BRANCH(Branch),
    .MEM_READ(MemRead),
    .MEM_TO_REG(MemtoReg),
    .MEM_WRITE(MemWrite),
    .ALU_SRC(ALUSrc),
    .REG_WRITE(RegWrite),
    .AuipcLui(AuipcLui_wire)
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

//REGISTROS PRIMERA FASE IF/ID  no hace falta registrarlos porque ya tenemos la rom  y el pc registrados

//REGISTROS SEGUNDA FASE ID/EX
reg [3:0] idata_ID_EX_30_12;
reg [4:0] idata_ID_EX_11_7;
reg [6:0] idata_ID_EX_6_0;
reg [ADDR_WIDTH-1:0] PC_ID_EX;
reg [ADDR_WIDTH:0] reg_imm_ID_EX;
reg Branch_ID_EX, MemWrite_ID_EX, MemRead_ID_EX, ALUSrc_ID_EX;
reg RegWrite_ID_EX;
reg [1:0] MemToReg_ID_EX;

wire [SIZE-1:0] imm_wire;

always_ff @( posedge CLK ) begin 

    idata_ID_EX_6_0 <= idata[6:0];

     //WB_PART
    RegWrite_ID_EX <= RegWrite;
    MemToReg_ID_EX <= MemtoReg;

        // M_PART
    Branch_ID_EX <= Branch;
    MemWrite_ID_EX <= MemWrite;
    MemRead_ID_EX <= MemRead;

    // EX_PART
    ALUSrc_ID_EX <= ALUSrc;
    
    PC_ID_EX <= PC;

    // REGISTRO DE PARTE DEL INMEDIATO
    reg_imm_ID_EX <= imm_wire; //lo que sale del generador de imm
    idata_ID_EX_30_12 <= {idata[30],idata[14:12]}; //idata[{30,14:12}];    
    idata_ID_EX_11_7  <= idata[11:7];    
    // data_1_wire_ID_EX <= data_1_wire; YA ESTÁ REGISTRADO EN BANCO DE REGISTROS
    // data_2_wire_ID_EX <= data_2_wire;
end   

//REGISTROS FASE EX/MEM
reg RegWrite_EX_MEM, Branch_EX_MEM, MemWrite_EX_MEM, MemRead_EX_MEM;
reg [1:0]MemToReg_EX_MEM;
reg [ADDR_WIDTH-1:0] branch_target_wire_EX_MEM;
reg [SIZE-1:0] address_alu_result_EX_MEM;
reg address_alu_zero_EX_MEM;
reg [SIZE-1:0] data_2_wire_EX_MEM;
reg [5:0] idata_EX_MEM_11_7;
reg [14:12] idata_EX_MEM_14_12;

wire [ADDR_WIDTH-1:0] branch_target_wire;
wire address_alu_zero;
wire [SIZE-1:0] address_alu_result;

always_ff @( posedge CLK ) begin 

    //WB_PART
    RegWrite_EX_MEM <= RegWrite_ID_EX;
    MemToReg_EX_MEM <= MemToReg_ID_EX;

    //M_PART
    Branch_EX_MEM <= Branch_ID_EX;
    MemWrite_EX_MEM <= MemWrite_ID_EX;
    MemRead_EX_MEM <= MemRead_ID_EX;

    branch_target_wire_EX_MEM <= branch_target_wire;

    address_alu_result_EX_MEM <= address_alu_result; // entrada del Address en la RAM daddr
    address_alu_zero_EX_MEM <= address_alu_zero;

    data_2_wire_EX_MEM <= data_2_wire; //entrada Write data (ddata_w) de la RAM
    idata_EX_MEM_11_7 <= idata_ID_EX_11_7; //Write Register que el entra al banco de registros
    idata_EX_MEM_14_12 <= idata_ID_EX_30_12[2:0];
end

assign iaddr = address_alu_result_EX_MEM;
assign idata = data_2_wire_EX_MEM;

//REGISTROS FASE MEM/WB
reg RegWrite_MEM_WB;
reg [2:0] MemtoReg_MEM_WB;
reg [ADDR_WIDTH-1:0] address_alu_result_MEM_WB;

always_ff @( posedge CLK ) begin
    //WB_PART
    RegWrite_MEM_WB <= RegWrite_EX_MEM;
    MemtoReg_MEM_WB <= MemToReg_EX_MEM;

    address_alu_result_MEM_WB <= address_alu_result_EX_MEM;
end



//Como hay que trocear la instruccion a mano, solo funciona para 32 bits

IMMEDIATE_GENERATOR imm_gen(
    .inst(idata),
    .IMMEDIATE(imm_wire)
);

// wire [SIZE-1:0] first_operand_wire;
// wire [SIZE-1:0] myInput_alu_src_1_mux [3];
// assign myInput_alu_src_1_mux[0] = PC;
// assign myInput_alu_src_1_mux[1] = 32'b0;
// assign myInput_alu_src_1_mux[2] = data_1_wire;

// MUX #(.SIZE(32), .INPUTS(3)) alu_src_1_mux (
//     .all_inputs(myInput_alu_src_1_mux),
//     .sel(AuipcLui_wire),
//     .result(first_operand_wire)
// );

wire [SIZE-1:0] second_operand_wire;
wire [SIZE-1:0] myInput_alu_src_2_mux [2];
assign myInput_alu_src_2_mux[0] = data_2_wire;
assign myInput_alu_src_2_mux[1] = reg_imm_ID_EX;//

MUX #(.SIZE(SIZE), .INPUTS(2)) alu_src_2_mux (
    .all_inputs(myInput_alu_src_2_mux),
    .sel(ALUSrc_ID_EX),
    .result(second_operand_wire)
);

wire [3:0] ALUSelection_wire;
ALU_CONTROL alu_control(
    .OPCODE(idata_ID_EX_6_0),
    .funct3(idata_ID_EX_30_12[2:0]),
    .bit30(idata_ID_EX_30_12[3]),
    .ALUSelection(ALUSelection_wire)
);



ALU #(.SIZE(SIZE)) address_alu(
    .A(data_1_wire),
    .B(second_operand_wire),
    .OPERATION(ALUSelection_wire),
    .RESULT(address_alu_result),
    .ZERO(address_alu_zero)
);

assign daddr = {2'b0, address_alu_result[31:2]};

wire [SIZE-1:0] myInput_data_mux [3];
assign myInput_data_mux[0] = address_alu_result_MEM_WB;
assign myInput_data_mux[1] = ddata_r;
assign myInput_data_mux[2] = {22'b0, next_consecutive_pc_wire[9:0]};

MUX #(.SIZE(SIZE), .INPUTS(3)) data_mux (
    .all_inputs(myInput_data_mux),
    .sel(MemtoReg),
    .result(data_mux_result_wire)
);


ALU #(.SIZE(ADDR_WIDTH)) jump_alu(
    .A(PC_ID_EX),
    .B(reg_imm_ID_EX),
    .OPERATION(ADD),
    .RESULT(branch_target_wire),
    .ZERO()
);

wire PCSrc;
assign PCSrc = Branch_EX_MEM & ((idata_EX_MEM_14_12[14:12] == 001 && !address_alu_zero_EX_MEM) || (idata_EX_MEM_14_12[14:12] != 001 && address_alu_zero_EX_MEM));

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


//Inst_IF (32bits) conectada a la rom
//1 ciclo después cuando llegue el flancod e reloj Inst_ID pasa a la siguienten fase

//always @(posedge CLK)
//Inst_ID <= Inst_IF //los 32 bits de la fase IF pasan a la fase ID para ser decodificada
