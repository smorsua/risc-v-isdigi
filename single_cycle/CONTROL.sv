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
        I_FORMAT: 
        S_FORMAT:
        B_FORMAT:
        U_FORMAT:
        J_FORMAT: 
        default: 
    endcase
end

endmodule