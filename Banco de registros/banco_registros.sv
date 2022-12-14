module banco_registros #(parameter SIZE = 32) (CLK,RESET,reg1r,reg2r,regW, writeData,RegWrite,Data1,Data2);
  
    input CLK,RESET;
    input logic [$clog2(SIZE)-1:0] reg1r, reg2r, regW; //seleccion de registro DIRECCIONES
    input logic [SIZE-1:0] writeData;
    input RegWrite;
    output logic [SIZE-1:0] Data1, Data2; //dentro de cada registro, X0,X1 etc selecciono los datos de 32bits de cada registro
 logic [SIZE-1:0][31:0] banco_registros;

//caso escritura
//cojo el valor de regW que es la direccion donde voy a escribir el dato que obtengo de la señal writeData 

always @(posedge CLK or negedge RESET)
begin 
    if(!RESET)
	 banco_registros <= '0;  

    else if(RegWrite && regW!='0)
        banco_registros[regW] <= writeData;

end     

//caso lectura

always_ff @(posedge CLK)
	begin
		Data1 <= banco_registros[reg1r];  
		Data2 <= banco_registros[reg2r];
	end


//assert property (@(posedge CLK) disable iff (RegWrite and regW!='0) |-> (writeData == banco_registros[regW])) else $error("No realiza correctamente la escritura")
endmodule







