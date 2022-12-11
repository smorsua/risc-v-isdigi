`ifndef IF_RAM_GUARD
`define IF_RAM_GUARD

interface if_ram;

logic [9:0] address;
logic [31:0] dato_entrada;
logic [31:0] dato_salida;
logic enable;

modport ram_module
(input address,
input enable,
input dato_entrada
output dato_salida);

modport main_circuit
(output address,
output enable,
input dato_salida
output dato_entrada);
endinterface
`endif //IF_RAM_GUARD
