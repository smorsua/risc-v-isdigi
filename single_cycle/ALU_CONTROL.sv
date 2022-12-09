`include "../ALU/operation_type.sv"
`include "instruction_type.sv"

module ALU_CONTROL(
    input [6:0] OPCODE,
    input [2:0] funct3,
    input bit30,
    output reg [3:0] ALUSelection
);

    always_comb begin
        casex(OPCODE)
        R_FORMAT: begin //tipo R
            case(funct3)
            3'b000: ALUSelection = bit30 == 0 ? ADD : SUB;
            3'b001: ALUSelection = LEFT_SHIFT_UNSIGNED;
            3'b010: ALUSelection = LESS_THAN_SIGNED;
            3'b011: ALUSelection = LESS_THAN_UNSIGNED;
            3'b100: ALUSelection = XOR;
            3'b101: ALUSelection = bit30 == 0 ? RIGHT_SHIFT_UNSIGNED : RIGHT_SHIFT_SIGNED;
            3'b110: ALUSelection = OR;
            3'b111: ALUSelection = AND;
			default: ALUSelection = 0;
            endcase
        end
        I_FORMAT: begin
            casex(OPCODE)
                7'b0000011: begin // instrucciones de carga
                    ALUSelection = ADD;
                end
                7'b001x011: begin // operaciones con immediatos
                    case(funct3)
                        3'b000: ALUSelection = ADD;
                        3'b001: ALUSelection = LEFT_SHIFT_UNSIGNED;
                        3'b010: ALUSelection = LESS_THAN_SIGNED;
                        3'b011: ALUSelection = LESS_THAN_UNSIGNED;
                        3'b100: ALUSelection = XOR;
                        3'b101:
                            case(bit30)
                            1'b0: ALUSelection = RIGHT_SHIFT_UNSIGNED;
                            1'b1: ALUSelection = RIGHT_SHIFT_SIGNED;
                            //FIXME: usar case sin default
                            default: ALUSelection = RIGHT_SHIFT_UNSIGNED;
                            endcase
                        3'b110: ALUSelection = OR;
                        3'b111: ALUSelection = AND;
								//usar case que no necesita default
							default: ALUSelection = ADD;
                    endcase
                end
					 //usar case que no necesita default
				default: ALUSelection = ADD;
            endcase

        end
        // S_FORMAT: ALUSelection = ADD;
        // B_FORMAT:
        U_FORMAT:begin
            casex(funct3)
                3'bxxx: ALUSelection = ADD;
            endcase
        end
        // J_FORMAT:
		  default: ALUSelection = 0;
    //FIXME: falta uno

        endcase
    end

endmodule