module ram
#(parameter data_width=32, parameter addr_width=10)
(
	input [(addr_width-1):0] ADRR_R, ADRR_W,
	input CLK, ENABLE_R, ENABLE_W,
    input  [(data_width-1):0] Q_W,
	output reg [(data_width-1):0] Q_R
);
	reg [data_width-1:0] ram[2**addr_width-1:0];


	always @ (ENABLE_R)
	begin
		Q_R <= ram[ADRR_R];
	
	end

    always @ (posedge CLK && ENABLE_W)
    begin
		ram[ADRR_W] <= Q_W ;
	
	end

    
endmodule