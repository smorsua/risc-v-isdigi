`include "../ALU/operation_type.sv"

module ALU_CONTROL(
    input [3:0] funct3,
    input bit30,
    input [1:0] ALUOp,
    output [3:0] ALUSelection
);

    always_comb begin
        case(ALUOp)
        2'b00: begin
            case(funct3)
            3'b000: ALUSelection = bit30 == 0 ? ADD : SUB;
            3'b001: ALUSelection = LEFT_SHIFT;
            3'b010: ALUSelection = LESS_THAN;
            3'b011: ALUSelection = LESS_THAN;
            3'b100: ALUSelection = XOR;
            3'b101: ALUSelection = bit30 == 0 ? RIGHT_SHIFT : SIGNED_RIGHT_SHIFT;
            3'b110: ALUSelection = OR;
            3'b111: ALUSelection = AND;
				default: ALUSelection = 0;
            endcase
        end
        2'b01: ALUSelection = SUB;
        2'b10: ALUSelection = ADD;
		  default: ALUSelection = 0;
    //FIXME: falta uno

        endcase
    end

endmodule