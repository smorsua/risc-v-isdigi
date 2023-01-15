module data_forwarding #(parameter SIZE=32) (
    input reg_write_mem, reg_write_ex, reg_write_wb, reg_write_wb_aux,
    input [4:0] rd_mem, rd_wb, rd_wb_aux,
    input [4:0] rs1_ex, rs2_ex,
    input [6:0] opcode_ex,
    output logic [1:0] forwardA, forwardB
);

//POR AHORA ESTAMOS REALIZANDO EL CONTROL DEL DATAPATH Y CREEMOS UNICAMENTE QUE ESTO SOLO FUNCIONA CON LAS R,S,B FORMAT
//DEBIDO A QUE SON LÁS ÚNICAS QUE TIENEN RS1 Y RS2. 
always_comb begin 
//RSB format
if(opcode_ex == 7'b0110011 || opcode_ex == 7'b0100011 || opcode_ex == 7'b1100011) begin
    if(reg_write_mem && (rd_mem != 0) && (rd_mem == rs1_ex))
        forwardA = 10;
    else if(reg_write_wb && (rd_wb != 0) && (rd_wb == rs1_ex))
        forwardA = 01;
    else if(reg_write_wb_aux && (rd_wb_aux != 0) && (rd_wb_aux == rs1_ex))
        forwardA = 11;
    else
        forwardA = 00;


    if(reg_write_mem && (rd_mem != 0) && (rd_mem == rs2_ex))
        forwardB = 10;
    else if(reg_write_wb && (rd_wb != 0) && (rd_wb == rs2_ex))
        forwardB = 01;
    else if(reg_write_wb_aux && (rd_wb_aux != 0) && (rd_wb_aux == rs2_ex))
        forwardB = 11;
    else
        forwardB = 00;
end
else if (opcode_ex == 7'b0010011) begin
    
    if(reg_write_mem && (rd_mem != 0) && (rd_mem == rs1_ex))
        forwardA = 10;
    else if(reg_write_wb && (rd_wb != 0) && (rd_wb == rs1_ex))
        forwardA = 01;
    else if(reg_write_wb_aux && (rd_wb_aux != 0) && (rd_wb_aux == rs1_ex))
        forwardA = 11;
    else
        forwardA = 00;
    
    forwardB = 00;
end
else begin
    forwardA = 00;
    forwardB = 00;
end
end





endmodule
