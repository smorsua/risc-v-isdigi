module jump_predictor #(parameter PC_SIZE = 12) (
    input CLK,
    input [6:0] opcode,
    input [PC_SIZE-1:0] previous_pc,
    input [PC_SIZE-1:0] next_consecutive_pc,
    input [PC_SIZE-1:0] jump_pc,
    input has_jumped,
    output [PC_SIZE-1:0] next_pc,
    output clear_if
);
const B_FORMAT_OP_CODE = 7'b1100011;

int iaddrToJumpPredictionCounter[int];
reg previousPrediction;
logic [PC_SIZE-1:0] predictedPc;
logic [PC_SIZE-1:0] pcInCaseOfWrongPrediction;


always_ff @(posedge CLK) begin
    if(previousPrediction == has_jumped) begin
        incrementPredictionCounter();
    end else begin
        decrementPredictionCounter();
    end
end

assign next_pc = getPrediction() ? jump_pc : next_consecutive_pc;
assign clear_if = opcode == B_FORMAT_OP_CODE;

task incrementPredictionCounter();
    if(iaddrToJumpPredictionCounter.has()) begin
        if(iaddrToJumpPredictionCounter[previous_pc] < 4) begin
            iaddrToJumpPredictionCounter[previous_pc] <= iaddrToJumpPredictionCounter[previous_pc] + 1;
        end
    end
endtask

task decrementPredictionCounter();
    if(iaddrToJumpPredictionCounter.has()) begin
        if(iaddrToJumpPredictionCounter[previous_pc] > 1) begin
            iaddrToJumpPredictionCounter[previous_pc] <= iaddrToJumpPredictionCounter[previous_pc] - 1;
        end
    end
endtask

function getPrediction();
    return opcode == B_FORMAT_OP_CODE && iaddrToJumpPrediction[current_pc].has() ? iaddrToJumpPrediction[current_pc] > 2 : 1;
endfunction
endmodule