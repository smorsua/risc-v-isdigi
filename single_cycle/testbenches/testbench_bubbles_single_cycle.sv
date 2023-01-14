 `timescale 1ns/1ps
module testbench_bubbles_single_cycle();
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
defparam rom_unregistered.file = "bubble.txt" ;

golden main(CLK, RESET_N, idata, iaddr, daddr, ddata_r, ddata_w, d_rw);
defparam main.ADDR_WIDTH = addr_width;
defparam main.SIZE = data_width;

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
        #(T*500);
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