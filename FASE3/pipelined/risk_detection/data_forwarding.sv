`ifndef DATA_FORWARDING_GUARD
`define DATA_FORWARDING_GUARD

`include "../../Shared/Control/instruction_type.sv"

module data_forwarding #(parameter SIZE) (
    input reg_write_mem, reg_write_ex, reg_write_wb, reg_write_wb_aux,
    input [4:0] rd_mem, rd_wb, rd_wb_aux,
    input [4:0] rs1_ex, rs2_ex,
    input [6:0] opcode_ex,
    output logic [1:0] forwardA, forwardB
);

//POR AHORA ESTAMOS REALIZANDO EL CONTROL DEL DATAPATH Y CREEMOS UNICAMENTE QUE ESTO SOLO FUNCIONA CON LAS R,S,B FORMAT
//DEBIDO A QUE SON LÁS ÚNICAS QUE TIENEN RS1 Y RS2. 
//HAY QUE ARREGLAR EL TEMA DE LAS S FORMAT, YA QUE TIENEN UNA PARTE DE INMEDIATO QUE SERIA EL RD, DE OTRAS SEÑALES 
// POR TANTO NO PODEMOS TRATARLA DE LA MISMA MANERA
// EN EL CASO DE LAS I FORMAT, SOLO TIENEN UN RS1, POR TANTO NO HAY QUE HACER NADA CON EL RS2, PERO TAMBIÉN TENEMOS QUE 

always_comb begin 
//RSB format
$display("-------------------- new instruction --------------------");
$display("opcode_ex: %b", opcode_ex);
$display("rs1_ex: %b", rs1_ex);
$display("rs2_ex: %b", rs2_ex);
$display("rd_mem: %b", rd_mem);
$display("rd_wb: %b", rd_wb);
$display("rd_wb_aux: %b", rd_wb_aux);
$display("reg_write_mem: %b", reg_write_mem);
$display("reg_write_wb: %b", reg_write_wb);
$display("reg_write_wb_aux: %b", reg_write_wb_aux);

casex (opcode_ex)
    R_FORMAT: begin
        r_format_and_b_format_forwarding();
        $display("R format");
    end
    B_FORMAT: begin
        r_format_and_b_format_forwarding();
        $display("B format");
    end
    S_FORMAT: begin
        s_format_forwarding();
        $display("S format");
    end
    I_FORMAT: begin
        i_format_forwarding();
        $display("I format");
    end
    default: begin
        forwardA = 2'b00;
        forwardB = 2'b00;
        $display("default");
    end
endcase
end


task r_format_and_b_format_forwarding();
    if(reg_write_mem && (rd_mem != 0) && (rd_mem == rs1_ex))
        forwardA = 2'b10;
    else if(reg_write_wb && (rd_wb != 0) && (rd_wb == rs1_ex))
        forwardA = 2'b01;
    else if(reg_write_wb_aux && (rd_wb_aux != 0) && (rd_wb_aux == rs1_ex))
        forwardA = 2'b11;
    else
        forwardA = 2'b00;


    if(reg_write_mem && (rd_mem != 0) && (rd_mem == rs2_ex))
        forwardB = 2'b10;
    else if(reg_write_wb && (rd_wb != 0) && (rd_wb == rs2_ex))
        forwardB = 2'b01;
    else if(reg_write_wb_aux && (rd_wb_aux != 0) && (rd_wb_aux == rs2_ex))
        forwardB = 2'b11;
    else
        forwardB = 2'b00;
endtask

task s_format_forwarding();
    if(reg_write_mem && (rd_mem != 0) && (rd_mem == rs1_ex))
        forwardA = 2'b10;
    else if(reg_write_wb && (rd_wb != 0) && (rd_wb == rs1_ex))
        forwardA = 2'b01;
    else if(reg_write_wb_aux && (rd_wb_aux != 0) && (rd_wb_aux == rs1_ex))
        forwardA = 2'b11;
    else
        forwardA = 2'b00;

    if(reg_write_mem && (rd_mem != 0) && (rd_mem == rs2_ex))
        forwardB = 2'b10;
    else if(reg_write_wb && (rd_wb != 0) && (rd_wb == rs2_ex))
        forwardB = 2'b01;
    else if(reg_write_wb_aux && (rd_wb_aux != 0) && (rd_wb_aux == rs2_ex))
        forwardB = 2'b11;
    else
        forwardB = 2'b00;
endtask

task i_format_forwarding();
    if(reg_write_mem && (rd_mem != 0) && (rd_mem == rs1_ex))
        forwardA = 2'b10;
    else if(reg_write_wb && (rd_wb != 0) && (rd_wb == rs1_ex))
        forwardA = 2'b01;
    else if(reg_write_wb_aux && (rd_wb_aux != 0) && (rd_wb_aux == rs1_ex))
        forwardA = 2'b11;
    else
        forwardA = 2'b00;
    
    forwardB = 2'b00;
endtask

endmodule
`endif
