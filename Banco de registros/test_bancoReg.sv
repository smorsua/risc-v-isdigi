
`timescale 1ns/1ps

module test_bancoReg();

	localparam T = 10;
	localparam SIZE = 32;

    reg CLK;
    reg [SIZE-1:0] reg1r, reg2r, regW; //seleccion de registro
    reg  [SIZE-1:0]writeData;
    reg RegWrite;
    wire [SIZE-1:0] Data1, Data2;

    //instancias 
     
    banco_registros DUV #(.SIZE(32))( 
    .CLK(CLK),
    .reg1r(reg1), 
    .reg2r(reg2), 
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

	initial begin
		RST_N = 0;
		#(T)
		RST_N = 1;


        //llenamos la memoria para que haya algun dato del que leer 
        banco_registros = [5'd13][5'd10]; //aqui tendría que indicar direccion de mem y contenido 

        reg1 = 5'd14; //indico dos direcciones
        reg2 = 5'd20;

	end

endmodule
