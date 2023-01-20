`timescale 1ns/1ps

`include "../memories/ram_registered.sv"
`include "../memories/rom_registered.sv"
`include "../pipelined.sv"

module testbench_pipelined();
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

ram_registered ram_registered(
    .CLK(CLK),
    .daddr(daddr),
    .MemWrite(MemWrite),
    .MemRead(MemRead),
    .ddata_w(ddata_w),
    .ddata_r(ddata_r));
defparam ram_registered.addr_width = addr_width;
defparam ram_registered.data_width = data_width;

wire rom_enable;
rom_registered rom_registered(.CLK(CLK), .enable(rom_enable), .iaddr(iaddr), .idata(idata));
defparam rom_registered.addr_width = addr_width;
defparam rom_registered.data_width = data_width;
defparam rom_registered.file = "test_jump_predictor.txt" ;

pipelined pipelined(
    .CLK(CLK),
    .RESET_N(RESET_N),
    .CLEAR(CLEAR),
    .idata(idata),
    .iaddr(iaddr),
    .rom_enable(rom_enable),
    .daddr(daddr),
    .ddata_r(ddata_r),
    .ddata_w(ddata_w),
    .mem_write(MemWrite),
    .mem_read(MemRead));

defparam pipelined.ADDR_SIZE = addr_width;
defparam pipelined.DATA_SIZE = data_width;

initial
begin
	CLK = 0;
	forever  #(T/2) CLK = ~CLK;
end

initial
    begin
        RESET_N = 0;
        CLEAR = 1;
		#(T/4)
		RESET_N = 1;
        CLEAR = 0;
        #(T*500);
        $stop;
    end

endmodule