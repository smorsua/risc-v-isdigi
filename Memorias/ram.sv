module RAM
#(parameter data_width=32, parameter addr_width=10)
(
	input CLK,
	input  [(addr_width-1):0] ADDR_W,
	input ENABLE_W, 
    input  [(data_width-1):0] Q_W,
	input [(addr_width-1):0] ADDR_R,
	output reg [(data_width-1):0] Q_R
);
	reg [data_width-1:0] ram[2**addr_width-1:0];



	assign 	Q_R = ram[ADDR_R] ;
	

    always @(posedge CLK)
    begin
	 if(ENABLE_W)
		ram[ADDR_W] <= Q_W ;
	
	end
	assert property (@(posedge CLK) ENABLE_W |=>  (ram[$past(ADDR_W, 1)] == $past(Q_W, 1))) else  $error ("No escribe");
endmodule