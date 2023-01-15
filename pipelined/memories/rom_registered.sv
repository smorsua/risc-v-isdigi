`ifndef ROM_REGISTERED_GUARD
`define ROM_REGISTERED_GUARD

module rom_registered
#(parameter data_width=32, parameter addr_width=10, parameter file)
(
	input CLK,
	input [addr_width - 1:0] iaddr,
	output reg [data_width - 1:0] idata
);

reg [data_width-1:0] rom[2**addr_width-1:0];
integer i;
initial			 
begin
    idata = 0;
    for(i=0; i < 2 ** addr_width; i++) begin
        rom[i] = 'b0;
    end
    $readmemh(file, rom);
end

always @(posedge CLK)
begin
    idata <= rom[iaddr];
end
	
endmodule

`endif