 `timescale 1ns/1ps

`include "../memories/ram_registered.sv"
`include "../memories/rom_registered.sv"
`include "../pipelined.sv"

module testbench_cochefantastico();
localparam  T = 20, addr_width = 10, data_width = 32;


logic CLK;
logic RESET_N;
logic CLEAR;

cochefantastico cochefantastico(
    .CLK(CLK),
    .RESET_N(RESET_N),
    .CLEAR(CLEAR)

    );
defparam cochefantastico.ADDR_SIZE = addr_width;
defparam cochefantastico.DATA_SIZE = data_width;

initial
begin
	CLK = 1;
	forever  #(T/2) CLK = ~CLK;
end

initial
    begin
        RESET_N = 0;
        CLEAR = 1;
		    #(T)
		RESET_N = 1;
        CLEAR = 0;
        #(T*100000);
        $stop;

    end

endmodule