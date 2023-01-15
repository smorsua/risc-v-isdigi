module data_forwarding #(parameter SIZE) (
    input reg_write_mem, reg_write_ex, reg_write_wb, reg_write_wb_aux,
    input [4:0] inst_11_to_7_mem, inst_11_to_7_wb, inst_11_to_7_wb_aux,
    input [4:0] inst_19_to_15_ex, inst_24_to_20_ex,
    output logic [1:0] forwardA, forwardB
);

//POR AHORA ESTAMOS REALIZANDO EL CONTROL DEL DATAPATH Y CREEMOS UNICAMENTE QUE ESTO SOLO FUNCIONA CON LAS R,S,B FORMAT
//DEBIDO A QUE SON LÁS ÚNICAS QUE TIENEN RS1 Y RS2. 
always_comb begin 

    if(reg_write_mem && (inst_11_to_7_mem != 0) && (inst_11_to_7_mem == inst_19_to_15_ex))
        forwardA = 10;
    else if(reg_write_wb && (inst_11_to_7_wb != 0) && (inst_11_to_7_wb == inst_19_to_15_ex))
        forwardA = 01;
    else if(reg_write_wb_aux && (inst_11_to_7_wb_aux != 0) && (inst_11_to_7_wb_aux == inst_19_to_15_ex))
        forwardA = 11;
    else
        forwardA = 00;


    if(reg_write_mem && (inst_11_to_7_mem != 0) && (inst_11_to_7_mem == inst_24_to_20_ex))
        forwardB = 10;
    else if(reg_write_wb && (inst_11_to_7_wb != 0) && (inst_11_to_7_wb == inst_24_to_20_ex))
        forwardB = 01;
    else if(reg_write_wb_aux && (inst_11_to_7_wb_aux != 0) && (inst_11_to_7_wb_aux == inst_19_to_15_ex))
        forwardB = 11;
    else
        forwardB = 00;
    
end





endmodule
