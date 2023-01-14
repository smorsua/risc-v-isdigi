 `timescale 1ns/1ps

`include "../single_cycle/single_cycle.sv"
`include "../single_cycle/memories/ram_unregistered.sv"
`include "../single_cycle/memories/rom_unregistered.sv"

`include "../pipelined/pipelined.sv"
`include "../pipelined/memories/ram_registered.sv"
`include "../pipelined/memories/ram_registered.sv"

module golden_test();
localparam  T = 20, addr_width = 10, data_width = 32;


logic CLK;
logic RESET_N;
logic CLEAR;
logic d_rw, d_rw_golden;
logic  [(data_width-1):0] ddata_w, ddata_w_golden;
logic [(addr_width-1):0] daddr, daddr_golden;
logic  [(data_width-1):0] ddata_r, ddata_r_golden;
logic [(addr_width-1):0] iaddr, iaddr_golden;
logic  [(data_width-1):0] idata, idata_golden;
logic  [(data_width-1):0] reg_write_data, reg_write_data_golden; //para comparar y comprobar banco reg
logic MemWrite, MemRead;

/*--------------------------------------------------------------------------------
 *  Pipelined
 *-------------------------------------------------------------------------------*/
ram_registered ram_registered(CLK, daddr, MemWrite, MemRead, ddata_w, ddata_r);
defparam ram_registered.addr_width = addr_width;
defparam ram_registered.data_width = data_width;

rom_registered rom_registered(.CLK(CLK), .iaddr(iaddr), .idata(idata));
defparam rom_registered.addr_width = addr_width;
defparam rom_registered.data_width = data_width;
defparam rom_registered.file = "fibonacci_pipelined.txt" ;

pipelined pipelined (CLK, RESET_N, CLEAR, idata, iaddr, daddr, ddata_r, ddata_w, MemWrite, MemRead,reg_write_data);
defparam pipelined.ADDR_SIZE = addr_width;
defparam pipelined.DATA_SIZE = data_width;

/*--------------------------------------------------------------------------------
 *  Golden Model
 *-------------------------------------------------------------------------------*/
ram_unregistered ram_unregistered(CLK, daddr_golden, d_rw_golden,ddata_w_golden, ddata_r_golden);
defparam ram_unregistered.addr_width = addr_width;
defparam ram_unregistered.data_width = data_width;

rom_unregistered rom_unregistered(.iaddr(iaddr_golden), .idata(idata_golden));
defparam rom_unregistered.addr_width = addr_width;
defparam rom_unregistered.data_width = data_width;
defparam rom_unregistered.file = "fibonacci.txt" ;

single_cycle single_cycle(CLK, RESET_N, idata_golden, iaddr_golden, daddr_golden, ddata_r_golden, ddata_w_golden, d_rw_golden, reg_write_data_golden);
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
        CLEAR = 1;
		    #(T/2)
		RESET_N = 1;
        CLEAR = 0;
        #(T*500);
        $stop;

    end


endmodule