module ROM
#(parameter data_width=32, parameter addr_width=10, parameter file = "bubble.txt")
(
	input CLK,
	input [(addr_width-1):0] iaddr,
	output reg [(data_width-1):0] idata
);
	reg [data_width-1:0] rom[2**addr_width-1:0];
	initial // Read the memory contents in the file
			 //dual_port_rom_init.txt. 
	begin
		$readmemh("bubble.txt", rom);
	end

	always_ff @(posedge CLK)
	begin
	 	idata <= rom[iaddr];
	end
	
endmodule