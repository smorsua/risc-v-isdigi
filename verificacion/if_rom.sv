`ifndef IF_ROM_GUARD
`define IF_ROM_GUARD

interface if_rom;

logic [9:0] iaddr;
logic [31:0] idata;

modport monitorizar
(input iaddr,
input idata);

modport duv
(input iaddr,
output idata);

modport main_circuit
(output iaddr,
input idata);
endinterface
`endif //IF_ROM_GUARD