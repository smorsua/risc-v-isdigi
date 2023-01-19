`ifndef HAZARD_DETECTION_GUARD
`define HAZARD_DETECTION_GUARD

module hazard_detection #(parameter SIZE = 32) (
    input [4:0] id_rs1,
    input [4:0] id_rs2,
    input mem_read_mem,
    input [4:0]rd_register_mem,
    input reg_write_mem,
    output reg PCWrite,
    output reg enable_nop_mux,
    output reg if_id_enable
);

always_comb begin

    if(mem_read_mem && reg_write_mem &&(rd_register_mem == id_rs1 || rd_register_mem == id_rs2)) begin
        PCWrite = 0;
        enable_nop_mux = 1;
        if_id_enable = 0;
    end else begin
        PCWrite = 1;
        enable_nop_mux = 0;
        if_id_enable = 1;
    end
end

endmodule

`endif

/*
una vez que hemos detectado que estamos dentro de una señal de load
lo que tenemos que hacer, es primero habilitar la ejecución de esa señal
posteriormente, en el siguietne ciclo pararíamos dicho ciclo el micro entero,
aunque realmente lo que estamos haciendo con esto es añadir un retraso.
Debemos congelar el pc, para que no siga sumando en ese momento de retraso, y además
deberíamos introducir en todas las señales de control un 0??? para así que pare.
Por tanto, tendríamos una salida seguro ahora mismo que es la de parada del pc,
y más salidas que serían las de congelado del micro en esa etapa.*/