`ifndef IF_RAM_GUARD
`define IF_RAM_GUARD

interface if_ram;

logic [9:0] daddr;
logic [31:0] ddata_w;
logic [31:0] ddata_r;
logic d_rw;

modport ram_module
(input daddr,
input d_rw,
input ddata_w,
output ddata_r);

modport main_circuit
(output daddr,
output d_rw,
input ddata_r,
output ddata_w);
endinterface
`endif //IF_RAM_GUARD
