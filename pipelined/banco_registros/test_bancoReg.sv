
`timescale 1ns/1ps

module test_bancoReg();

	localparam T = 10;
	localparam SIZE = 32;

    logic CLK,RESET_N;
    logic [$clog2(SIZE)-1:0] read_reg1, read_reg2, write_reg; //seleccion de registro DIRECCIONES
    logic [SIZE-1:0] writeData;
	logic RegWrite;
    logic [SIZE-1:0] Data1, Data2; //dentro de cada registro, X0,X1 etc selecciono los datos de 32bits de cada registro

    //instancias 
     
    banco_registros_registered #(.SIZE(SIZE)) DUV (CLK, RESET_N, read_reg1, read_reg2, write_reg, writeData, RegWrite, Data1, Data2);


	initial
	begin
		CLK = 0;
		forever  #(T/2) CLK=!CLK;
	end 


	initial
	begin
		RESET_N = 0;
		#(T)
		RESET_N = 1;

   		RegWrite =1'b1;
	
    		write_reg = 5'd10;
    		writeData = 5'd21;
			#(T*2)
    		write_reg = 5'd14;
    		writeData = 5'd13;
			#(T*2)
   		write_reg = 5'd7;
   		writeData = 5'd1;
    		writeData = 5'd6;
			#(T*2)

    
    		read_reg1 = 5'd14; 
    		read_reg2 = 5'd10;
			#(T*2)

	$stop;
	end
endmodule
