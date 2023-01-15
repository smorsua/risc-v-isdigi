`ifndef BANCO_REGISTROS_UNREGISTERED_GUARD
`define BANCO_REGISTROS_UNREGISTERED_GUARD

module banco_registros_unregistered #(parameter SIZE = 32) (
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


// problema a considerar: lectura y escritura del mismo registro 
//asertions
// assert property (@(posedge CLK) disable iff (RegWrite and write_reg!='0) |-> (writeData == banco_registros[write_reg])) else $error("No realiza correctamente la escritura")
//no sé si debería utilizar ##1 para así seleccionar diferentes ciclos, osea muestrear writeData 
//del ciclo anterior con lo que me saca banco_registros[regW] en el ciclo actual
endmodule 

`endif






