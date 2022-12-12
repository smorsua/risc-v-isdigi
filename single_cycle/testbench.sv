 `timescale 1ns/1ps
module testbench();
localparam  T = 20, addr_width = 10, data_width = 32;


logic CLK;
logic RESET_N;
logic ENABLE_W;
logic  [(data_width-1):0] Q_W;
logic [(addr_width-1):0] ADDR_RAM;
logic  [(data_width-1):0] Q_RAM;
logic [(addr_width-1):0] ADDR_ROM;
logic  [(data_width-1):0] Q_ROM;

RAM ram(CLK, ADDR_RAM, ENABLE_W, Q_W, ADDR_RAM, Q_RAM);
defparam ram.addr_width = addr_width;
defparam ram.data_width = data_width;

ROM rom(.ADDR_R(ADDR_ROM), .Q_R(Q_ROM));
defparam rom.addr_width = addr_width;
defparam rom.data_width = data_width;
defparam rom.file = "instructions.txt" ;

top top(CLK, RESET_N, Q_ROM, ADDR_ROM, ADDR_RAM, Q_RAM, Q_W, ENABLE_W);
defparam top.ADDR_WIDTH = addr_width;
defparam top.SIZE = data_width;

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
        #(T*700);
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