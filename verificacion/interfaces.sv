interface if_rom;

logic [9:0] address;
logic [31:0] dato;

modport monitorizar
(input address,
input dato);

modport testar
(output address,
input dato);

modport duv
(input address,
output dato);
endinterface