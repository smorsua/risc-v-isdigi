`ifndef JUMP_PREDICTOR_GUARD
`define JUMP_PREDICTOR_GUARD

`include "../../Shared/Control/instruction_type.sv"

module jump_predictor #(parameter PC_SIZE = 12) (
    input CLK,
    input [6:0] opcode,
    input [PC_SIZE-1:0] current_pc,
    input [PC_SIZE-1:0] next_consecutive_pc,
    input [PC_SIZE-1:0] jump_pc,
    input should_have_jumped,
    output do_jump,
    output reg [PC_SIZE-1:0] predictor_jump_pc,
    output clear_if
);

integer iaddrToJumpPredictionCounter [logic[PC_SIZE-1]];

reg previous_prediction;
reg had_to_correct_mistake;
reg [PC_SIZE-1:0] previous_pc;
wire prediction_was_correct;

logic [PC_SIZE-1:0] pcInCaseOfWrongPrediction;

initial begin
    previous_prediction = 0;
    had_to_correct_mistake = 0;
    previous_pc = 0;
    pcInCaseOfWrongPrediction = 0;
end


always @(posedge CLK) begin
    if(prediction_was_correct) begin
        incrementPredictionCounter();
    end else begin
        decrementPredictionCounter();
    end
    previous_pc <= current_pc;
    previous_prediction <= shouldPredictJump();
    had_to_correct_mistake <= prediction_was_correct;
end
    
assign prediction_was_correct = previous_prediction == should_have_jumped;
assign do_jump = shouldPredictJump();

always_comb begin
    if(prediction_was_correct || had_to_correct_mistake) begin
        predictor_jump_pc = shouldPredictJump() ? jump_pc : next_consecutive_pc;
    end else begin
        predictor_jump_pc = pcInCaseOfWrongPrediction;
    end
end

assign clear_if = opcode == B_FORMAT || opcode == J_FORMAT || !prediction_was_correct;

function shouldPredictJump();
    return opcode == J_FORMAT || (opcode == B_FORMAT && iaddrToJumpPredictionCounter.exists(current_pc) ? iaddrToJumpPredictionCounter[current_pc] > 2 : 1);
endfunction

task incrementPredictionCounter();
    if(iaddrToJumpPredictionCounter.exists(previous_pc)) begin
        if(iaddrToJumpPredictionCounter[previous_pc] < 4) begin
            iaddrToJumpPredictionCounter[previous_pc] = iaddrToJumpPredictionCounter[previous_pc] + 1;
        end
    end
endtask

task decrementPredictionCounter();
    if(iaddrToJumpPredictionCounter.exists(previous_pc)) begin
        if(iaddrToJumpPredictionCounter[previous_pc] > 1) begin
            iaddrToJumpPredictionCounter[previous_pc] = iaddrToJumpPredictionCounter[previous_pc] - 1;
        end
    end
endtask

endmodule

`endif