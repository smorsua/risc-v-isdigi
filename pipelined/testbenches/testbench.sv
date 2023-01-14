 `timescale 1ns/1ps

`include "../memories/ram_registered.sv"
`include "../memories/rom_registered.sv"
`include "../pipelined.sv"

module testbench();
localparam  T = 20, addr_width = 10, data_width = 32;


logic CLK;
logic RESET_N;
logic CLEAR;
logic MemWrite, MemRead;
logic  [(data_width-1):0] ddata_w;
logic [(addr_width-1):0] daddr;
logic  [(data_width-1):0] ddata_r;
logic [(addr_width-1):0] iaddr;
logic  [(data_width-1):0] idata;

ram_registered ram_registered(CLK, daddr, MemWrite, MemRead, ddata_w, ddata_r);
defparam ram_registered.addr_width = addr_width;
defparam ram_registered.data_width = data_width;

rom_registered rom_registered(.CLK(CLK), .iaddr(iaddr), .idata(idata));
defparam rom_registered.addr_width = addr_width;
defparam rom_registered.data_width = data_width;
defparam rom_registered.file = "instructions.txt" ;

pipelined pipelined(CLK, RESET_N, CLEAR, idata, iaddr, daddr, ddata_r, ddata_w, MemWrite, MemRead);
defparam pipelined.ADDR_SIZE = addr_width;
defparam pipelined.DATA_SIZE = data_width;

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
        //load_program("instructions.txt");
        #(T*100000);
        $stop;

    end

/*task  read(input [addr_width-1:0] address_read, input [7:0] cicles = 1);
    ADDR_ROM = address_read; //error con dependiendo version questa
endtask*/

task load_program(input file);
begin
@(negedge CLK)
file = "instructions.txt" ;
@(negedge CLK);
end
endtask

endmodule