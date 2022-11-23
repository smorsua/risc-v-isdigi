module MUX #(parameter SIZE = 32) (
    input [SIZE-1:0] A,
    input [SIZE-1:0] B,
    input SEL,
    output [SIZE-1:0] result
);

assign result = SEL == 0 ? A : B;

endmodule