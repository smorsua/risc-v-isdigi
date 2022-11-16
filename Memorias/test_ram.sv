`timescale 1ns/1ps
localparam  T = 5, addr_width = 10, data_width = 32;




module test_ram (

);

logic [(addr_width-1):0] ADRR_R, ADRR_W;
logic CLK, ENABLE_R, ENABLE_W;
logic  [(data_width-1):0] Q_W;
logic [(data_width-1):0] Q_R;

ram ram(ADRR_R, ADRR_W, CLK, ENABLE_R, ENABLE_W, Q_W, Q_R);
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
    read(2);
    fork
    begin
        read(2,4);
        write(2);
   
    end
    join

    $stop;
	
end
task  read(input [addr_width-1:0] address_read, input [7:0] cicles = 1); 
    ENABLE_R = 1;
    ADRR_R = address_read; 
    #(cicles*T)
    ENABLE_R = 0;
endtask //automatic

task  write(input [addr_width-1:0] address_write);
    ENABLE_W = 1; 
    @(negedge CLK)
    ADRR_W = address_write;
    Q_W = $random();
    @(negedge CLK); 
    ENABLE_W = 0; 
endtask
endmodule
