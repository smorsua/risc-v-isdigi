
`include "Scoreboard.sv"

`timescale 1ns/1ps
module tb_ifaces();
parameter addr_width = 10; 
parameter data_width = 32;

localparam T = 20; 

logic CLK, RESET_N, CLEAR;

// inicializamos la interfaz
ifaces iface(.CLK(CLK), .RESET_N(RESET_N), .CLEAR(CLEAR));
Scoreboard scoreboard;
/*--------------------------------------------------------------------------------
 *  Pipelined
 *-------------------------------------------------------------------------------*/

ram ram(
    .CLK(iface.memories.CLK), 
    .daddr(iface.memories.daddr), 
    .MemWrite(iface.memories.MemWrite), 
    .MemRead(iface.memories.MemRead), 
    .ddata_w(iface.memories.ddata_w), 
    .ddata_r(iface.memories.ddata_r));
defparam ram.addr_width = addr_width;
defparam ram.data_width = data_width;

rom rom(
    .CLK(iface.memories.CLK), 
    .iaddr(iface.memories.iaddr), 
    .idata(iface.memories.idata));
defparam rom.addr_width = addr_width;
defparam rom.data_width = data_width;
defparam rom.file = "fibonacci_pipelined.txt" ;

main pipelined (
    .CLK(iface.pipelined.CLK), 
    .RESET_N(iface.pipelined.RESET_N), 
    .CLEAR(iface.pipelined.CLEAR), 
    .idata(iface.pipelined.idata), 
    .iaddr(iface.pipelined.iaddr), 
    .daddr(iface.pipelined.daddr), 
    .ddata_r(iface.pipelined.ddata_r), 
    .ddata_w(iface.pipelined.ddata_w), 
    .mem_write(iface.pipelined.MemWrite), 
    .mem_read(iface.pipelined.MemRead));
defparam pipelined.ADDR_SIZE = addr_width;
defparam pipelined.DATA_SIZE = data_width;

ram_golden ram_golden(
    .CLK(iface.memories.CLK), 
    .d_rw(iface.memories.d_rw_golden), 
    .daddr(iface.memories.daddr_golden), 
    .ddata_w(iface.memories.ddata_w_golden),
    .ddata_r(iface.memories.ddata_r_golden));
defparam ram_golden.addr_width = addr_width;
defparam ram_golden.data_width = data_width;

rom_golden rom_golden(.iaddr(iface.memories.iaddr_golden), .idata(iface.memories.idata_golden));
defparam rom_golden.addr_width = addr_width;
defparam rom_golden.data_width = data_width;
defparam rom_golden.file = "fibonacci.txt" ;

golden golden (
    .CLK(CLK), 
    .RESET_N(RESET_N),
    .idata(iface.golden.idata_golden), 
    .iaddr(iface.golden.iaddr_golden), 
    .daddr(iface.golden.daddr_golden), 
    .ddata_r(iface.golden.ddata_r_golden), 
    .ddata_w(iface.golden.ddata_w_golden), 
    .d_rw(iface.golden.d_rw_golden));
defparam golden.ADDR_WIDTH = addr_width;
defparam golden.SIZE = data_width;


initial
begin
    scoreboard = new(iface.monitor, golden.registros.writeData);

    fork
        scoreboard.monitor_input();
    join_none

	CLK = 0;
	forever  #(T/2) CLK = ~CLK;
end

initial
    begin
        RESET_N = 0;
        CLEAR = 1;
		    #(T/2)
		RESET_N = 1;
        CLEAR = 0;
        #(T*500);
        $stop;

    end


endmodule