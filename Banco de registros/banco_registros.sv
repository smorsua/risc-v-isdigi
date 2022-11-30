module banco_registros #(parameter SIZE = 32) (CLK,RESET,reg1r,reg2r,regW, writeData,RegWrite,Data1,Data2);
  
    input CLK,RESET;
    input logic [$clog2(SIZE)-1:0] reg1r, reg2r, regW; //seleccion de registro DIRECCIONES
    input logic [SIZE-1:0] writeData;
    input RegWrite;
    output logic [SIZE-1:0] Data1, Data2; //dentro de cada registro, X0,X1 etc selecciono los datos de 32bits de cada registro
 logic [SIZE-1:0][31:0] banco_registros;

//X0,X1,X2... primer[] indica el numero de registros, el segundo indica la long de cada registro
//tamaño de palabra fijo, profundidad de palabra parametrizable para ram y rom en el banco de registro es fijo 


//caso escritura
//cojo el valor de regW que es la direccion donde voy a escribir el dato que obtengo de la señal writeData 

always @(posedge CLK or negedge RESET)
begin 
    if(!RESET)
	 banco_registros <= '0; 
       // for (int i = 0; i < SIZE-1; i = i+1)
		// banco_registros[i] <= '0; 

    else if(RegWrite && regW!='0)
        banco_registros[regW] <= writeData;
//    else 
//	banco_registros[regW] <= writeData;
//		
end     

//caso lectura

assign Data1 = banco_registros[reg1r];
assign Data2 = banco_registros[reg2r];

// problema a considerar: lectura y escritura del mismo registro 
//asertions
assert property (@(posedge CLK) disable iff (RegWrite and regW!='0) |-> (writeData == banco_registros[regW])) else $error("No realiza correctamente la escritura")
//no sé si debería utilizar ##1 para así seleccionar diferentes ciclos, osea muestrear writeData 
//del ciclo anterior con lo que me saca banco_registros[regW] en el ciclo actual
endmodule 







