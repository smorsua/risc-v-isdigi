module banco_registro ( #(parameter SIZE = 32)
    input CLK;
    input [SIZE-1:0] reg1r, reg2r, regW; //seleccion de registro
    input  [SIZE-1:0]writeData;
    input RegWrite;
    output [SIZE-1:0] Data1, Data2; //dentro de cada registro, X0,X1 etc selecciono los datos de 32bits de cada registro
);

logic  [SIZE-1:0][SIZE-1:0] banco_registros;  //X0,X1,X2...


//caso lectura
assign banco_registros [reg1r] = Data1;
assign banco_registros [reg2r] = Data2;

//caso escritura
//cojo el valor de regW que es la direccion donde voy a escribir el dato que obtengo de la señal writeData 
always_ff @(posedge CLK)
begin
    if(RegWrite)
    banco_registros [regW] = writeData;
    else 
    
end


// problema a considerar: lectura y escritura del mismo registro 

endmodule 

