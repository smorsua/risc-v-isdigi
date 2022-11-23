`timescale 1ns/1ps
localparam  T = 20, addr_width = 10, data_width = 32;




module test_ram (

);

	logic CLK,
	logic  [(addr_width-1):0] ADRR_W,
	logic ENABLE_W,
    logic  [(data_width-1):0] Q_W,
	logic [(addr_width-1):0] ADRR_R,
	logic reg [(data_width-1):0] Q_R

ram ram(CLK, ADRR_W, ENABLE_W, Q_W, ADRR_R, Q_R);
defparam ram.addr_width = addr_width;
defparam ram.data_width = data_width;

initial begin
    CLK = 0;
    forever #(T/2) CLK = !CLK;
end

/*initial 
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
        ADRR_R = 2;
        #(T);
        end
        begin 
        ADRR_W = 2;
        Q_W = $random();
        ENABLE_W = 1;
        #(2*T);
        ENABLE_W = 0; 
        end
    
    join
    #(T*2)
    $stop;
	
end*/
task  read(input [addr_width-1:0] address_read, input [7:0] cicles = 1); 
   
    ADRR_R = address_read; 
    #(cicles*T)
endtask 

task  write(input [addr_width-1:0] address_write);
    @(negedge CLK)
    ENABLE_W = 1; 
    Q_W = $random();
    ADRR_W = address_write;
    @(negedge CLK); 
    ENABLE_W = 0; 
endtask
endmodule