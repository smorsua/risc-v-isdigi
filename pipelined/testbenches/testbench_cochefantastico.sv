 `timescale 1ns/1ps

`include "../memories/ram_registered.sv"
`include "../memories/rom_registered.sv"
`include "../pipelined.sv"

module testbench_cochefantastico();
localparam  T = 20, addr_width = 10, data_width = 32;


logic CLK;
logic RESET_N;
logic CLEAR;
logic [7:0]LED;
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
defparam rom_registered.file = "./leds_placa.txt" ;

cochefantastico cochefantastico(
    .CLK(CLK),
    .RESET_N(RESET_N),
    .CLEAR(CLEAR),
    .idata(idata),
    .iaddr(iaddr),
    .daddr(daddr),
    .ddata_r(ddata_r),
    .ddata_w(ddata_w),
    .mem_write(mem_write),
    .mem_read(mem_read),
    .reg_write_data(),
    .reg_write_enable(),
    .write_register(),
    .LED(LED)
    );
defparam placa.ADDR_SIZE = addr_width;
defparam placa.DATA_SIZE = data_width;

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