 `timescale 1ns/1ps


`include "../SINGLE_CYCLE_FILES/single_cycle/golden.sv"
`include "../SINGLE_CYCLE_FILES/Memorias/ram_golden.sv"
`include "../SINGLE_CYCLE_FILES/Memorias/rom_golden.sv"

`include "../PIPELINED_FILES/pipelined/main.sv"
`include "../PIPELINED_FILES/Memorias/ram.sv"
`include "../PIPELINED_FILES/Memorias/rom.sv"
module golden_test();
localparam  T = 20, addr_width = 10, data_width = 32;


logic CLK;
logic RESET_N;
logic CLEAR
logic d_rw, d_rw_golden;
logic  [(data_width-1):0] ddata_w, ddata_w_golden;
logic [(addr_width-1):0] daddr, daddr_golden;
logic  [(data_width-1):0] ddata_r, ddata_r_golden;
logic [(addr_width-1):0] iaddr, iaddr_golden;
logic  [(data_width-1):0] idata, idata_golden;
logic MemWrite,MemRead;

//pipelined
ram ram(CLK, daddr, MemWrite, MemRead, ddata_w, ddata_r);
defparam ram.addr_width = addr_width;
defparam ram.data_width = data_width;

rom rom(.CLK(CLK), .iaddr(iaddr), .idata(idata));
defparam rom.addr_width = addr_width;
defparam rom.data_width = data_width;
defparam rom.file = "fibonacci.txt" ;

main pipelined (CLK, RESET_N, CLEAR, idata, iaddr, daddr, ddata_r, ddata_w, MemWrite, MemRead);
defparam main.ADDR_SIZE = addr_width;
defparam main.DATA_SIZE = data_width;

//single_cycle_
ram_golden ram_golden(CLK, daddr_golden, d_rw_golden,ddata_w_golden, ddata_r_golden);
defparam ram_golden.addr_width = addr_width;
defparam ram_golden.data_width = data_width;

rom_golden rom_golden(.iaddr(iaddr_golden), .idata(idata_golden));
defparam rom_golden.addr_width = addr_width;
defparam rom_golden.data_width = data_width;
defparam rom_golden.file = "fibonacci.txt" ;

golden golden(CLK, RESET_N, idata_golden, iaddr_golden, daddr_golden, ddata_r_golden, ddata_w_golden, d_rw_golden);
defparam golden.ADDR_WIDTH = addr_width;
defparam golden.SIZE = data_width;


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