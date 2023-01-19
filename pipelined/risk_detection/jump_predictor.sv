`ifndef JUMP_PREDICTOR_GUARD
`define JUMP_PREDICTOR_GUARD

`include "../../Shared/Control/instruction_type.sv"


module jump_predictor #(parameter PC_SIZE = 12) (
    input CLK,
    input RESET_N,
    input [6:0] opcode,
    input [PC_SIZE - 1:0] current_pc,
    input [PC_SIZE - 1:0] next_consecutive_pc,
    input [PC_SIZE - 1:0] jump_pc,
    input should_have_jumped,
    output reg do_jump,
    output reg [PC_SIZE - 1:0] predictor_jump_pc,
    output force_nop
);

const logic initialPrediction = 1;

reg [1:0] jumpAddrToPredictionCounter[(2 ** PC_SIZE) - 1:0];
reg previous_prediction;
reg [PC_SIZE-1:0] previous_jump_pc;
reg [PC_SIZE-1:0] pcInCaseOfWrongPrediction; 
reg isRecoveringFromMistake; // If we predicted a jump but it didn't happen, we need to recover from that mistake
wire prediction_was_correct;

integer i;
initial begin
    previous_prediction = 0;
    previous_jump_pc = 0;
    pcInCaseOfWrongPrediction = 0;
    for(i = 0; i < $size(jumpAddrToPredictionCounter); i += 1) begin
        jumpAddrToPredictionCounter[i] = initialPrediction;        
    end
end

assign prediction_was_correct = previous_prediction == should_have_jumped;

// Update jump_table
always @(posedge CLK) begin    
    if(previous_prediction) begin
        if(prediction_was_correct) begin
            incrementPredictionCounter();            
        end else begin
            decrementPredictionCounter();            
        end
    end else begin
        if(prediction_was_correct) begin
            decrementPredictionCounter();            
        end else begin
            incrementPredictionCounter();            
        end        
    end
end

// Update rest of variables
always @(posedge CLK) begin
    isRecoveringFromMistake <= !prediction_was_correct;
    previous_jump_pc <= jump_pc;
    previous_prediction <= isLikelyToJump();
    pcInCaseOfWrongPrediction <= isLikelyToJump() ? next_consecutive_pc : jump_pc;
end

always_comb do_jump = (isLikelyToJump() || !prediction_was_correct) && !isRecoveringFromMistake;

always_comb predictor_jump_pc = getPredictorJumpPc();

assign force_nop = !prediction_was_correct;

wire isLikelyToJumpWire;
assign isLikelyToJumpWire = isLikelyToJump();
function bit isLikelyToJump();
    return opcode == J_FORMAT || (opcode == B_FORMAT && jumpAddrToPredictionCounter[jump_pc] >= 2);
endfunction

function logic[PC_SIZE - 1:0] getPredictorJumpPc();
    if(prediction_was_correct) begin
        return isLikelyToJump() ? jump_pc : next_consecutive_pc;        
    end else begin
        return pcInCaseOfWrongPrediction;
    end
endfunction

task incrementPredictionCounter();
    if(jumpAddrToPredictionCounter[previous_jump_pc] < 3) begin
        jumpAddrToPredictionCounter[previous_jump_pc] <= jumpAddrToPredictionCounter[previous_jump_pc] + 1;
    end
endtask

task decrementPredictionCounter();
    if(jumpAddrToPredictionCounter[previous_jump_pc] > 0) begin
        jumpAddrToPredictionCounter[previous_jump_pc] <= jumpAddrToPredictionCounter[previous_jump_pc] - 1;
    end
endtask

endmodule

`endif