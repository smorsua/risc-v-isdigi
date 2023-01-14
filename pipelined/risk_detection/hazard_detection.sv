module hazard_detection #(parameter SIZE = 32) (

input CLK,
input [SIZE-1 : 0] instruction,
output logic PC_frozen,
output CLEAR,
output enable_mux
);

logic clear_aux;
/*
una vez que hemos detectado que estamos dentro de una señal de load
lo que tenemos que hacer, es primero habilitar la ejecución de esa señal 
posteriormente, en el siguietne ciclo pararíamos dicho ciclo el micro entero,
aunque realmente lo que estamos haciendo con esto es añadir un retraso. 
Debemos congelar el pc, para que no siga sumando en ese momento de retraso, y además
deberíamos introducir en todas las señales de control un 0??? para así que pare.
Por tanto, tendríamos una salida seguro ahora mismo que es la de parada del pc, 
y más salidas que serían las de congelado del micro en esa etapa.*/   

always_ff @(posedge CLK) begin

    if ( (instruction[14:12] == 3'b010) && (instruction[6:0] == 7'b0000011) ) begin
        clear_aux <= 1'b1;
    end
    else  begin
        clear_aux <= 1'b0; 
    end

end
assign CLEAR = clear_aux;

always_comb begin
    if ( (instruction[14:12] == 3'b010) && (instruction[6:0] == 7'b0000011) ) begin
    PC_frozen = 1'b1;
    enable_mux =1'b1;

    end
    else  begin
        PC_frozen = 1'b0; 
        enable_mux =1'b0;o0
    end
end


endmodule
