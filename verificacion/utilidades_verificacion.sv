package utilidades_verificacion;

typedef mailbox #(logic [31:0]) instruction_box;

class RCSG_RISCV; 
  rand logic [31:0] valor;
  constraint R_format    {valor[6:0] == 7'b0110011;}
  constraint R_format_a  {(valor[6:0] == 7'b0110011 && valor[14:12]!=3'b000 && valor[14:12]!=3'b101) -> valor[31:25]==7'b0000000 ;}
  constraint R_format_b  {(valor[6:0] == 7'b0110011 && (valor[14:12]==3'b000) || valor[14:12]==3'b101) -> valor[31:25]==7'b0000000 || valor[31:25]==7'b0100000 ;}
  
  constraint I_format      {valor[6:0] == 7'b0010011 || valor[6:0] == 7'b0000011;}
  constraint I_format_a    {valor[6:0] == 7'b0010011 -> valor[14:12] != 3'b001 && valor[14:12] != 3'b101 ;} //000, 010,011, 100, 110 111
  constraint I_format_b    {valor[6:0] == 7'b0000011 -> valor[14:12] == 3'b010;}

  constraint S_format    {valor[6:0] == 7'b0100011 -> valor[14:12] == 3'b010;}
  constraint B_format    {valor[6:0] == 7'b1100011 -> valor[14:12] == 3'b000 || valor[14:12] == 3'b001;}
  constraint U_format    {valor[6:0] == 7'b0010111 || valor[6:0] ==7'b0110111;} 
  // constraint J_format    {valor[6:0] == 7'b1101111;}
  
endclass

class covergroups_RISCV;
virtual if_rom.monitorizar monitor_port;
covergroup instrucciones ;

  rformat : coverpoint ({monitor_port.dato[30],monitor_port.dato[14:12]})  iff (monitor_port.dato[6:0]==7'b0110011 && monitor_port.dato[31]==1'b0 && monitor_port.dato[29:25]==5'b0000)
  {
      bins add = {0};
      bins sub = {8};      
      bins sll = {1};
      bins slt = {2};
      bins sltu = {3};
      bins ixor = {4};
      bins slr = {5};
      bins sra = {13};
      bins ior = {6};
      bins iand = {7};
      illegal_bins imposibles_rformat = {9,10,11,12,14,15}; 
  } 

  iformat : coverpoint ({monitor_port.dato[4],monitor_port.dato[14:12]}) iff (monitor_port.dato[6:0]==7'b0000011 || monitor_port.dato[6:0]==7'b0010011)
  {
      bins addi = {8};//1000  
      bins slti = {10};//1010
      bins sltiu = {11}; //1011
      bins xori = {12};//1100
      bins ori = {14};//1110
      bins andi = {15};//1111   
      bins lw  = {2}; //0010
      illegal_bins imposibles_iformat_a = {0,1,3,4,5,6,7,9,13}; 
  } 


sformat : coverpoint ({monitor_port.dato[13]})  iff (monitor_port.dato[6:0]==7'b0100011)
  {
     

      bins sw={1};  //010
      illegal_bins imposibles_sformat = {0}
  } 


bformat : coverpoint ({monitor_port.dato[12]})  iff (monitor_port.dato[6:0]==7'b1100011)
  {
      bins beq ={0}; //000
      bins bne ={1};  //001 
  } 


uformat : coverpoint ({monitor_port.dato[5]}) iff (monitor_port.dato[6:0]==7'b0010111 || monitor_port.dato[6:0]==7'b0110111)
  {
      bins lui ={1};
      bins auipc ={0};
  } 

endgroup

function new(virtual if_rom.monitorizar mpuertos);
	monitor_port=mpuertos;
	instrucciones=new;
endfunction 
endclass	

endpackage