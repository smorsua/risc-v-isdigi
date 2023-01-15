`ifndef JUMP_PREDICTOR_GUARD
`define JUMP_PREDICTOR_GUARD

`include "../../Shared/Control/instruction_type.sv"

module jump_predictor #(parameter PC_SIZE = 12) (
    input CLK,
    input [6:0] opcode,
    input [PC_SIZE - 1:0] current_pc,
    input [PC_SIZE - 1:0] next_consecutive_pc,
    input [PC_SIZE - 1:0] jump_pc,
    input should_have_jumped,
    output reg do_jump,
    output reg [PC_SIZE - 1:0] predictor_jump_pc
);

logic[1:0] iaddrToJumpPredictionCounter[(2 ** PC_SIZE) - 1:0];

reg previous_prediction;
reg had_to_correct_mistake;
reg [PC_SIZE-1:0] previous_pc;
wire prediction_was_correct;

logic [PC_SIZE-1:0] pcInCaseOfWrongPrediction;

integer i;
initial begin
    previous_prediction = 0;
    had_to_correct_mistake = 0;
    previous_pc = 0;
    pcInCaseOfWrongPrediction = 0;
    for(i = 0; i < $size(iaddrToJumpPredictionCounter); i += 1) begin
        iaddrToJumpPredictionCounter[i] = 1;        
    end
end


always @(posedge CLK) begin
    if(prediction_was_correct) begin
        incrementPredictionCounter();
    end else begin
        decrementPredictionCounter();
    end
    previous_pc <= current_pc;
    previous_prediction <= shouldPredictJump();
    had_to_correct_mistake <= !prediction_was_correct;
end
    
assign prediction_was_correct = previous_prediction == should_have_jumped;

always_comb do_jump = shouldPredictJump() || should_have_jumped;

always_comb predictor_jump_pc = getPredictorJumpPc();

always @(posedge CLK) begin
    pcInCaseOfWrongPrediction <= shouldPredictJump() ? next_consecutive_pc : jump_pc;
end

function bit shouldPredictJump();
    automatic integer predictionCounter = iaddrToJumpPredictionCounter[current_pc] > 2;
    return opcode == J_FORMAT || (opcode == B_FORMAT && predictionCounter);
endfunction

function logic[PC_SIZE - 1:0] getPredictorJumpPc();
    if(prediction_was_correct || had_to_correct_mistake) begin
        return shouldPredictJump() ? jump_pc : next_consecutive_pc;
    end else begin
        return pcInCaseOfWrongPrediction;
    end
endfunction

task incrementPredictionCounter();
    if(iaddrToJumpPredictionCounter[previous_pc] < 4) begin
        iaddrToJumpPredictionCounter[previous_pc] = iaddrToJumpPredictionCounter[previous_pc] + 1;
    end
endtask

task decrementPredictionCounter();
    if(iaddrToJumpPredictionCounter[previous_pc] > 1) begin
        iaddrToJumpPredictionCounter[previous_pc] = iaddrToJumpPredictionCounter[previous_pc] - 1;
    end
endtask

endmodule

`endif