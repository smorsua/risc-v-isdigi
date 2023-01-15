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

typedef enum logic {
    PREDICTING,
    FIXING
} jump_predictor_state;

//PREDICTING = 0, FIXING = 1
jump_predictor_state state, next_state;
reg [1:0] nop_counter;
reg [1:0] iaddrToJumpPredictionCounter[(2 ** PC_SIZE) - 1:0];
reg previous_prediction;
reg [PC_SIZE-1:0] previous_pc;
reg [PC_SIZE-1:0] pcInCaseOfWrongPrediction;
wire prediction_was_correct;

integer i;
initial begin
    state = PREDICTING;
    nop_counter = 0;
    previous_prediction = 0;
    previous_pc = 0;
    pcInCaseOfWrongPrediction = 0;
    for(i = 0; i < $size(iaddrToJumpPredictionCounter); i += 1) begin
        iaddrToJumpPredictionCounter[i] = 1;        
    end
end

// Update state
always @(posedge CLK or negedge RESET_N) begin
    if(!RESET_N) begin
        state <= PREDICTING;                
    end else begin
        state <= next_state;        
    end
end

// Update next_state
always_comb begin
    case(state)
    PREDICTING: begin
        if(prediction_was_correct) begin
            next_state = PREDICTING;
        end else begin
            next_state = FIXING;
        end
    end
    FIXING: begin
        if(nop_counter == 0) begin
            next_state = PREDICTING;            
        end else begin
            next_state = FIXING;                    
        end
    end
    default: begin
        next_state = PREDICTING;                    
    end
    endcase
end

wire should_have_jumped_predictor;
assign should_have_jumped_predictor = should_have_jumped && state == PREDICTING;
assign prediction_was_correct = previous_prediction == should_have_jumped_predictor;

// Update nop_counter
always @(posedge CLK) begin
    case(state)
    PREDICTING: begin
        if(prediction_was_correct) begin
            nop_counter <= 0;            
        end else begin
            nop_counter <= 2;                        
        end
    end
    FIXING: begin
        nop_counter <= nop_counter - 1;
    end
    default: begin
        nop_counter <= 0;    
    end
    endcase
end

// Update jump_table
always @(posedge CLK) begin
    case(state)
    PREDICTING: begin
        if(prediction_was_correct) begin
            incrementPredictionCounter();
        end else begin
            decrementPredictionCounter();
        end
    end
    FIXING: begin
        iaddrToJumpPredictionCounter[previous_pc] <= iaddrToJumpPredictionCounter[previous_pc];
    end
    default: iaddrToJumpPredictionCounter[previous_pc] <= iaddrToJumpPredictionCounter[previous_pc];
    endcase
end

// Update rest of variables
always @(posedge CLK) begin
    previous_pc <= current_pc;
    previous_prediction <= isLikelyToJump();
    pcInCaseOfWrongPrediction <= isLikelyToJump() ? next_consecutive_pc : jump_pc;
end

assign force_nop = prediction_was_correct;

always_comb do_jump = isLikelyToJump() || !prediction_was_correct;

always_comb predictor_jump_pc = getPredictorJumpPc();

function bit isLikelyToJump();
    return opcode == J_FORMAT || (opcode == B_FORMAT && iaddrToJumpPredictionCounter[current_pc] > 2);
endfunction

function logic[PC_SIZE - 1:0] getPredictorJumpPc();
    case(state)
    PREDICTING: begin
        if(prediction_was_correct) begin
            return isLikelyToJump() ? jump_pc : next_consecutive_pc;        
        end else begin
            return pcInCaseOfWrongPrediction;
        end
    end
    default: return 0;
    endcase
endfunction

task incrementPredictionCounter();
    if(iaddrToJumpPredictionCounter[previous_pc] < 4) begin
        iaddrToJumpPredictionCounter[previous_pc] <= iaddrToJumpPredictionCounter[previous_pc] + 1;
    end
endtask

task decrementPredictionCounter();
    if(iaddrToJumpPredictionCounter[previous_pc] > 1) begin
        iaddrToJumpPredictionCounter[previous_pc] <= iaddrToJumpPredictionCounter[previous_pc] - 1;
    end
endtask

endmodule

`endif