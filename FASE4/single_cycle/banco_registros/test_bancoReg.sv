
`timescale 1ns/1ps

module test_bancoReg();

	localparam T = 10;
	localparam SIZE = 32;

    logic CLK,RST_N;
    logic [$clog2(SIZE)-1:0] reg1r, reg2r, regW; //seleccion de registro
    logic  [SIZE-1:0]writeData;
    logic RegWrite;
    logic [SIZE-1:0] Data1, Data2;

    //instancias 
     
    banco_registros_golden #(.SIZE(SIZE)) DUV ( 
	 .RESET(RST_N),
    .CLK(CLK),
    .reg1r(reg1r), 
    .reg2r(reg2r), 
    .regW(regW), //seleccion de registro
    .writeData(writeData),
    .RegWrite(RegWrite),
    .Data1(Data1), 
    .Data2(Data2)
    );


	initial
	begin
		CLK = 0;
		forever  #(T/2) CLK=!CLK;
	end 


	initial
	begin
		RST_N = 0;
		#(T)
		RST_N = 1;

   		RegWrite =1'b1;
	
    		regW = 5'd10;
    		writeData = 5'd21;
			#(T*2)
    		regW = 5'd14;
    		writeData = 5'd13;
			#(T*2)
   		regW = 5'd7;
   		writeData = 5'd1;
    		writeData = 5'd6;
			#(T*2)

    
    		reg1r = 5'd14; 
    		reg2r = 5'd10;
			#(T*2)

	$stop;
	end
endmodule
