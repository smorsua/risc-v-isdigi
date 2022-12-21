`timescale 1ns/1ps


module test_ram (

);

localparam  T = 20, addr_width = 10, data_width = 32;

	logic CLK;
	logic  [(addr_width-1):0] daddr;
	logic d_rw;
    logic  [(data_width-1):0] ddata_w;
	logic [(data_width-1):0] ddata_r;

RAM_golden ram(CLK, daddr, d_rw, ddata_w, ddata_r);
defparam ram.addr_width = addr_width;
defparam ram.data_width = data_width;

initial begin
    CLK = 0;
    forever #(T/2) CLK = !CLK;
end

initial 
begin
	write(0);
    read(0);
    write(1);
    write(2);
    read(1);
    #(T/4)
    read(2);
    #(T/2)
    @(negedge CLK)
    fork
        begin
        daddr = 2;
        #(T);
        end
        begin 
        write(2);
        write(2);
        end
    
    join
    #(T*2)
    $stop;
	
end
task  read(input [addr_width-1:0] address_read, input [7:0] cicles = 1); 
   
    daddr = address_read; 
    #(cicles*T);
endtask 

task  write(input [addr_width-1:0] address_write);
    @(negedge CLK)
    d_rw = 1; 
    ddata_w = $random();
    daddr = address_write;
    @(negedge CLK); 
    d_rw = 0; 
endtask
endmodule
