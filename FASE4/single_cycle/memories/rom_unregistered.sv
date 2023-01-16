`ifndef ROM_UNREGISTERED_GUARD
`define ROM_UNREGISTERED_GUARD

module rom_unregistered
#(parameter data_width=32, parameter addr_width=10, parameter file = "rom_init.txt")
(
	input [(addr_width-1):0] iaddr,
	output reg [(data_width-1):0] idata
);
	reg [data_width-1:0] rom[2**addr_width-1:0];
	integer i;
	initial // Read the memory contents in the file
			 //dual_port_rom_init.txt. 
	begin
		for(i=0; i < 2 ** addr_width; i++) begin
			rom[i] = 00;
		end
		$readmemh(file, rom);
	
	end
	
	assign idata = rom[iaddr];
endmodule

`endif