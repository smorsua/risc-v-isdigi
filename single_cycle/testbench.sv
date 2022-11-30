 `timescale 1ns/1ps
module tetbench();
localparam  T = 20, addr_width = 10, data_width = 32;


logic CLK;
logic RESET_N;
logic  [(addr_width-1):0] ADDR_W;
logic ENABLE_W; 
logic  [(data_width-1):0] Q_W;
logic [(addr_width-1):0] ADDR_RAM;
logic  [(data_width-1):0] Q_RAM;
logic [(addr_width-1):0] ADDR_ROM;
logic  [(data_width-1):0] Q_ROM;

initial begin
    CLK = 0;
    forever #(T/2) CLK = !CLK;
end

RAM ram(CLK, ADDR_W, ENABLE_W, Q_W, ADDR_RAM, Q_RAM);
defparam ram.addr_width = addr_width;
defparam ram.data_width = data_width;

ROM rom(.ADDR_R(ADDR_ROM), .Q_R(Q_ROM));
defparam rom.addr_width = addr_width;
defparam rom.data_width = data_width;

top top(CLK, RESET_N, Q_ROM, ADDR_ROM, ADDR_RAM, Q_RAM, Q_W, ENABLE_W); //FALTAN SEÑALES POR METER PARA CONECTAR A LA RAM Y LA ROM
defparam top.SIZE = addr_width;
defparam top.ADDR_WIDTH = data_width;

initial begin
    
end







endmodule 