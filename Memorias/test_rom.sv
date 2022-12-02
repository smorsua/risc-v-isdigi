`timescale 1ns/1ps
localparam  T = 20, addr_width = 10, data_width = 32;




module test_rom (

);

	logic [(addr_width-1):0] ADDR_R;
	logic [(data_width-1):0] Q_R;

ROM rom(.ADDR_R(ADDR_R), .Q_R(Q_R));
defparam rom.addr_width = addr_width;
defparam rom.data_width = data_width;

initial 
begin
    
    read(0);
    read(1);
    read(2);
    $stop;
	
end
task  read(input [addr_width-1:0] address_read); 
    ADDR_R = address_read; 
endtask 


endmodule