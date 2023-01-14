`ifndef CONTROL_GUARD
`define CONTROL_GUARD

`include "instruction_type.sv"

module CONTROL(
    input [6:0] OPCODE,
    output reg BRANCH,
    output reg MEM_READ,
    output reg [1:0] MEM_TO_REG,
    output reg MEM_WRITE,
    output reg ALU_SRC,
    output reg REG_WRITE,
    output reg [1:0] AuipcLui
);


always_comb begin
    casex (OPCODE)
        R_FORMAT: begin
            BRANCH = 0;
            MEM_READ = 0; // X
            MEM_TO_REG = 0;
            MEM_WRITE = 0;
            ALU_SRC = 0;
            REG_WRITE = 1;
            AuipcLui = 2;
        end
        I_FORMAT: begin
            BRANCH = 0;
            MEM_WRITE = 0;
            ALU_SRC = 1;
            REG_WRITE = 1;
            AuipcLui = 2;
            casex(OPCODE)
                7'b0000011: begin
                    MEM_TO_REG = 1;
                    MEM_READ = 1;                    
                end  //Intrucciones de carga
                7'b001x011: begin
                    MEM_TO_REG = 0;
                    MEM_READ = 0; 
                end                    
            default: begin
                MEM_TO_REG = 0;
                MEM_READ = 0; 
            end
            endcase
            
             end
        S_FORMAT: begin
            BRANCH = 0;
            MEM_READ = 1;
            MEM_TO_REG = 0; //X
            MEM_WRITE = 1;
            ALU_SRC = 1;
            REG_WRITE = 0;
            AuipcLui = 2;
        end
        B_FORMAT: begin
            BRANCH = 1;
            MEM_READ = 0; //X
            MEM_TO_REG = 0; //X
            MEM_WRITE = 0;
            ALU_SRC = 0;
            REG_WRITE = 0;
            AuipcLui = 2;
        end
        U_FORMAT: begin
            case(OPCODE)
            //AUIPC
            'b0010111: begin
                BRANCH = 0;
                MEM_READ = 1;
                MEM_TO_REG = 0;
                MEM_WRITE = 0;
                ALU_SRC = 1;
                REG_WRITE = 1;
                AuipcLui = 0;
            end
            //LUI
            'b0110111: begin
                BRANCH = 0;
                MEM_READ = 1;
                MEM_TO_REG = 0;
                MEM_WRITE = 0;
                ALU_SRC = 1;
                REG_WRITE = 1;
                AuipcLui = 1;
            end
            default: begin
			BRANCH = 0;
            MEM_READ = 0;
            MEM_TO_REG = 0;
            MEM_WRITE = 0;
            ALU_SRC = 0;
            REG_WRITE = 0;
            AuipcLui = 0;
			end
            endcase

            end
       J_FORMAT: begin
            BRANCH = 1;
            MEM_READ = 0;
            MEM_TO_REG = 2;
            //ALU_OP = 'b10;
            MEM_WRITE = 0;
            ALU_SRC = 1;
            REG_WRITE = 1;
            AuipcLui = 0;
        end
        default:
			begin
			BRANCH = 0;
            MEM_READ = 0;
            MEM_TO_REG = 0;
            MEM_WRITE = 0;
            ALU_SRC = 0;
            REG_WRITE = 0;
            AuipcLui = 0;
			end
    endcase
end

endmodule
`endif