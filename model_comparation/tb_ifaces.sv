`include "../single_cycle/single_cycle.sv"
`include "../single_cycle/memories/ram_unregistered.sv"
`include "../single_cycle/memories/rom_unregistered.sv"

`include "../pipelined/pipelined.sv"
`include "../pipelined/memories/ram_registered.sv"
`include "../pipelined/memories/ram_registered.sv"

`include "Scoreboard.sv"
`include "ifaces.sv"

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

ram_registered ram_registered(
    .CLK(iface.memories.CLK),
    .daddr(iface.memories.daddr),
    .MemWrite(iface.memories.MemWrite),
    .MemRead(iface.memories.MemRead),
    .ddata_w(iface.memories.ddata_w),
    .ddata_r(iface.memories.ddata_r));
defparam ram_registered.addr_width = addr_width;
defparam ram_registered.data_width = data_width;

rom_registered rom_registered(
    .CLK(iface.memories.CLK),
    .iaddr(iface.memories.iaddr),
    .idata(iface.memories.idata));
defparam rom_registered.addr_width = addr_width;
defparam rom_registered.data_width = data_width;
defparam rom_registered.file = "./fibonacci_pipelined.txt" ;

pipelined pipelined (
    .CLK(iface.pipelined.CLK),
    .RESET_N(iface.pipelined.RESET_N),
    .CLEAR(iface.pipelined.CLEAR),
    .idata(iface.pipelined.idata),
    .iaddr(iface.pipelined.iaddr),
    .daddr(iface.pipelined.daddr),
    .ddata_r(iface.pipelined.ddata_r),
    .ddata_w(iface.pipelined.ddata_w),
    .mem_write(iface.pipelined.MemWrite),
    .mem_read(iface.pipelined.MemRead),
    .reg_write_data(iface.pipelined.reg_write_data),
    .reg_write_enable(iface.pipelined.reg_write_enable),
    .write_register(iface.pipelined.write_register));
defparam pipelined.ADDR_SIZE = addr_width;
defparam pipelined.DATA_SIZE = data_width;

ram_unregistered ram_unregistered(
    .CLK(iface.memories.CLK),
    .d_rw(iface.memories.d_rw_golden),
    .daddr(iface.memories.daddr_golden),
    .ddata_w(iface.memories.ddata_w_golden),
    .ddata_r(iface.memories.ddata_r_golden));
defparam ram_unregistered.addr_width = addr_width;
defparam ram_unregistered.data_width = data_width;

rom_unregistered rom_unregistered(.iaddr(iface.memories.iaddr_golden), .idata(iface.memories.idata_golden));
defparam rom_unregistered.addr_width = addr_width;
defparam rom_unregistered.data_width = data_width;
defparam rom_unregistered.file = "./fibonacci.txt" ;

single_cycle single_cycle (
    .CLK(CLK),
    .RESET_N(RESET_N),
    .idata(iface.golden.idata_golden),
    .iaddr(iface.golden.iaddr_golden),
    .daddr(iface.golden.daddr_golden),
    .ddata_r(iface.golden.ddata_r_golden),
    .ddata_w(iface.golden.ddata_w_golden),
    .d_rw(iface.golden.d_rw_golden),
    .reg_write_data(iface.golden.reg_write_data_golden),
    .reg_write_enable(iface.golden.reg_write_enable_golden),
    .write_register(iface.golden.write_register_golden));
defparam single_cycle.ADDR_WIDTH = addr_width;
defparam single_cycle.SIZE = data_width;


initial
begin
    scoreboard = new(iface.monitor);

    fork
        scoreboard.monitor_input();
        scoreboard.monitor_output();
    join_none

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
        #(T*1000);
        $stop;
    end


endmodule