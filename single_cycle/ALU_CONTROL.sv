module ALU_CONTROL(
    input [3:0] funct3,
    input bit30,
    input ALUOp,
    output [3:0] ALUSelection
);

    `include "ALU/operation_type.sv"
    always_comb begin
        case(ALUOp)
        2'b00: begin
            case(funct3)
            3'b000: ALUSelection = bit30 == 0 ? ADD : SUB; 
            3'b001: ALUSelection = LEFT_SHIFT;
            3'b010: ALUSelection = LESS_THAN;
            3'b011: ALUSelection = LESS_THAN;
            3'b100: ALUSelection = XOR;
            3'b101: ALUSelection = bit30 == 0 ? RIGHT_SHIFT : RIGHT_SHIFT; //FIXME: LA SEGUNDA VERSION EXTIENDE EL SIGNO
            3'b110: ALUSelection = OR;
            3'b111: ALUSelection = AND;
            endcase
        end
        endcase
    end

endmodule 