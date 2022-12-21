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
logic d_rw;
logic  [(data_width-1):0] ddata_w;
logic [(addr_width-1):0] daddr;
logic  [(data_width-1):0] ddata_r;
logic [(addr_width-1):0] iaddr;
logic  [(data_width-1):0] idata;

//pipelined
ram ram(CLK, daddr, d_rw,ddata_w, ddata_r);
defparam ram.addr_width = addr_width;
defparam ram.data_width = data_width;

rom rom(.iaddr(iaddr), .idata(idata));
defparam rom.addr_width = addr_width;
defparam rom.data_width = data_width;
defparam rom.file = "instructions.txt" ;

main main(CLK, RESET_N, idata, iaddr, daddr, ddata_r, ddata_w, d_rw);
defparam main.ADDR_SIZE = addr_width;
defparam main.DATA_SIZE = data_width;

//single_cycle_
ram_golden ram_golden(CLK, daddr, d_rw,ddata_w, ddata_r);
defparam ram_golden.addr_width = addr_width;
defparam ram_golden.data_width = data_width;

rom_golden rom_golden(.iaddr(iaddr), .idata(idata));
defparam rom_golden.addr_width = addr_width;
defparam rom_golden.data_width = data_width;
defparam rom_golden.file = "instructions.txt" ;

golden golden(CLK, RESET_N, idata, iaddr, daddr, ddata_r, ddata_w, d_rw);
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
		    #(T)
		RESET_N = 1;
        #(T*500);
        $stop;

    end





endmodule