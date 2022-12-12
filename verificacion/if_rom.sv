`ifndef IF_ROM_GUARD
`define IF_ROM_GUARD

interface if_rom;

logic [9:0] address;
logic [31:0] dato;

modport monitorizar
(input address,
input dato);

modport duv
(input address,
output dato);

modport main_circuit
(output address,
input dato);
endinterface
`endif //IF_ROM_GUARD