`ifndef MUX_GUARD
`define MUX_GUARD
module MUX #(parameter SIZE = 32, INPUTS = 4) (
    input [SIZE - 1:0] all_inputs [INPUTS],
    input [$clog2(INPUTS)-1:0] sel,
    output [SIZE-1:0] result
);

assign result = all_inputs[sel];

endmodule
`endif // MUX_GUARD