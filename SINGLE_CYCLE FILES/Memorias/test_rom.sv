`timescale 1ns/1ps

module test_rom (

);

localparam  T = 20, addr_width = 10, data_width = 32;

	logic CLK;
	logic [(addr_width-1):0] iaddr;
	logic [(data_width-1):0] idata;

ROM rom(.iaddr(iaddr), .idata(idata));
defparam rom.addr_width = addr_width;
defparam rom.data_width = data_width;

initial 
begin
	
    read(0);
    
    read(1);
    #(T/4)
    read(2);
    #(T/2)
    $stop;
	
end
task  read(input [addr_width-1:0] address_read, input [7:0] cicles = 1); 
    iaddr = address_read; 
endtask 


endmodule