module CONTROL(
    input [6:0] INSTRUCTION_FORMAT,
    output BRANCH,
    output MEM_READ,
    output MEM_TO_REG,
    output [1:0] ALU_OP,
    output MEM_WRITE,
    output ALU_SRC,
    output REG_WRITE
);
//FIXME: esto no funcionara hasta que el enum de los formatos de instruccion no sea global
always_comb begin
    case (INSTRUCTION_FORMAT)
        R_FORMAT: begin
            BRANCH = 0;
            MEM_READ = 0; // X
            MEM_TO_REG = 0;
            ALU_OP = 'b00;
            MEM_WRITE = 0;
            ALU_SRC = 0;
            REG_WRITE = 1;
        end
        I_FORMAT: begin
            BRANCH = 0;
            MEM_READ = 1;
            MEM_TO_REG = 1;
            ALU_OP = 'b10;
            MEM_WRITE = 0;
            ALU_SRC = 1;
            REG_WRITE = 1;
        end
        S_FORMAT:
        begin
            BRANCH = 0;
            MEM_READ = 0; //X
            MEM_TO_REG = 0;
            ALU_OP = 'b10;
            MEM_WRITE = 1;
            ALU_SRC = 1;
            REG_WRITE = 0;
        end
        B_FORMAT:
        begin
            BRANCH = 1;
            MEM_READ = 0; //X
            MEM_TO_REG = 0; //X
            ALU_OP = 'b01;
            MEM_WRITE = 0;
            ALU_SRC = 0;
            REG_WRITE = 0;
        end
        U_FORMAT: // creo que igual que I FORMAT
        begin
            BRANCH = 0;
            MEM_READ = 1;
            MEM_TO_REG = 1;
            ALU_OP = 'b10;
            MEM_WRITE = 0;
            ALU_SRC = 1;
            REG_WRITE = 1;
        end
        J_FORMAT: 
        begin
            BRANCH = 0;
            MEM_READ = 1;
            MEM_TO_REG = 1;
            ALU_OP = 'b10;
            MEM_WRITE = 0;
            ALU_SRC = 1;
            REG_WRITE = 1;
        end
        default: 
    endcase
end

endmodule