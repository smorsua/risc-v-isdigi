module ram
#(parameter data_width=32, parameter addr_width=10)
(
	input CLK,
	input  [(addr_width-1):0] ADRR_W,
	input ENABLE_W,
    input  [(data_width-1):0] Q_W,
	input [(addr_width-1):0] ADRR_R,
	output reg [(data_width-1):0] Q_R
);
	reg [data_width-1:0] ram[2**addr_width-1:0];



	assign 	Q_R = ram[ADRR_R];
	

    always @ (posedge CLK && ENABLE_W)
    begin
		ram[ADRR_W] <= Q_W ;
	
	end

endmodule