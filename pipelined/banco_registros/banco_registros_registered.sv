`ifndef BANCO_REGISTROS_REGISTERED_GUARD
`define BANCO_REGISTROS_REGISTERED_GUARD

module banco_registros_registered #(parameter SIZE = 32) (CLK, RESET_N, read_reg1, read_reg2, write_reg, writeData, RegWrite, Data1, Data2);

 
    input CLK,RESET_N;
    input logic [$clog2(SIZE)-1:0] read_reg1, read_reg2, write_reg; //seleccion de registro DIRECCIONES
    input logic [SIZE-1:0] writeData;
    input RegWrite;
    output logic [SIZE-1:0] Data1, Data2; //dentro de cada registro, X0,X1 etc selecciono los datos de 32bits de cada registro
 logic [SIZE-1:0][31:0] banco_registros;

//caso escritura
//cojo el valor de regW que es la direccion donde voy a escribir el dato que obtengo de la señal writeData 

always @(posedge CLK or negedge RESET_N)
begin 
    if(!RESET_N)
	 banco_registros <= '0;
    else if(RegWrite && write_reg !== '0)
        banco_registros[write_reg] <= writeData;

end     

//caso lectura

always_ff @(posedge CLK or negedge RESET_N)
	begin
        if(!RESET_N) begin
            Data1 <= 0;
            Data2 <= 0;
        end else begin
            Data1 <= banco_registros[read_reg1];  
            Data2 <= banco_registros[read_reg2];            
        end
	end


//assert property (@(posedge CLK) disable iff (RegWrite and regW!='0) |-> (writeData == banco_registros[regW])) else $error("No realiza correctamente la escritura")
endmodule

`endif  






