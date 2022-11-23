module ROM
#(parameter data_width=32, parameter addr_width=10)
(
	input [(addr_width-1):0] ADDR_R,
	output reg [(data_width-1):0] Q_R
);
	reg [data_width-1:0] rom[2**addr_width-1:0];
	initial // Read the memory contents in the file
			 //dual_port_rom_init.txt. 
	begin
		$readmemb("rom_init.txt", rom);
	end


	assign Q_R = rom[ADDR_R];
	


    
endmodule