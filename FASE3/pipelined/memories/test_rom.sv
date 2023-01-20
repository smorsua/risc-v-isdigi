`include "./rom_registered.sv"

`timescale 1ns/1ps

module test_rom ();

localparam  T = 20, addr_width = 10, data_width = 32;

	logic CLK;
	logic [(addr_width-1):0] iaddr;
	logic [(data_width-1):0] idata;

rom_registered rom_registered(.CLK(CLK), .iaddr(iaddr), .idata(idata));
defparam rom_registered.addr_width = addr_width;
defparam rom_registered.data_width = data_width;


initial begin
    CLK = 0;
    forever #(T/2) CLK = !CLK;
end


initial 
begin
	
    read(CLK, 0, 1);
    read(CLK, 1, 1);
    read(CLK, 2, 1);
    read(CLK, 3, 1);

    $stop;
	
end
task automatic read(ref CLK, input [addr_width-1:0] address_read, input [7:0] cicles = 1); 
    @(negedge CLK) begin
        iaddr <= address_read;
        #cicles;
    end
endtask 


endmodule