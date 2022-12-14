module BANCO_REGISTROS #(parameter SIZE = 32) (
    CLK,
    RESET_N,
    read_reg1,
    read_reg2,
    write_reg,
    writeData,
    RegWrite,
    Data1,
    Data2);
    
    input CLK, RESET_N;
    input logic [$clog2(SIZE)-1:0] read_reg1, read_reg2, write_reg;
    input logic [SIZE-1:0] writeData;
    input RegWrite;
    output logic [SIZE-1:0] Data1, Data2; 
 logic [SIZE-1:0][31:0] banco_registros;

always @(posedge CLK or negedge RESET_N)
begin 
    if(!RESET_N)
	    banco_registros <= '0; 
    else if(RegWrite && write_reg != '0)
        banco_registros[write_reg] <= writeData;
end  

assign Data1 = banco_registros[read_reg1];
assign Data2 = banco_registros[read_reg2];

//caso lectura

// problema a considerar: lectura y escritura del mismo registro 
//asertions
//assert property (@(posedge CLK) disable iff (RegWrite & regW!='0) |-> (writeData == banco_registros[regW])) else $error("No realiza correctamente la escritura")
//no sé si debería utilizar ##1 para así seleccionar diferentes ciclos, osea muestrear writeData 
//del ciclo anterior con lo que me saca banco_registros[regW] en el ciclo actual
endmodule 







