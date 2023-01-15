`include "../memories/ram_unregistered.sv"
`include "../memories/rom_unregistered.sv"
`include "../single_cycle.sv"

`timescale 1ns/1ps
module testbench_fibonacci_single_cycle();
localparam  T = 20, addr_width = 10, data_width = 32;


logic CLK;
logic RESET_N;
logic d_rw;
logic  [(data_width-1):0] ddata_w;
logic [(addr_width-1):0] daddr;
logic  [(data_width-1):0] ddata_r;
logic [(addr_width-1):0] iaddr;
logic  [(data_width-1):0] idata;

ram_unregistered ram_unregistered(CLK, daddr, d_rw, ddata_w, ddata_r);
defparam ram_unregistered.addr_width = addr_width;
defparam ram_unregistered.data_width = data_width;

rom_unregistered rom_unregistered(.iaddr(iaddr), .idata(idata));
defparam rom_unregistered.addr_width = addr_width;
defparam rom_unregistered.data_width = data_width;
defparam rom_unregistered.file = "./fibonacci.txt" ;

single_cycle single_cycle(CLK, RESET_N, idata, iaddr, daddr, ddata_r, ddata_w, d_rw);
defparam single_cycle.ADDR_WIDTH = addr_width;
defparam single_cycle.SIZE = data_width;

initial
begin
	CLK = 0;
	forever  #(T/2) CLK = ~CLK;
end

initial
    begin
        RESET_N = 0;
		    #(T)
		RESET_N = 1;
        //load_program("instructions.txt");
        #(T*1000);
        $stop;

    end

endmodule