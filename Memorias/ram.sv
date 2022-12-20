module RAM
#(parameter data_width=32, parameter addr_width=10)
(
	input CLK,
	input  [(addr_width-1):0] daddr,
	input MemWrite, MemRead,
    input  [(data_width-1):0] ddata_w,
	output reg [(data_width-1):0] ddata_r
);
	reg [data_width-1:0] ram[2**addr_width-1:0];

	integer i;
	initial begin
		ddata_r = 0;
		for(i=0; i < 2 ** addr_width; i++) begin
			ram[i] = 'b0;
		end
	end

    always @(posedge CLK)
    begin
	 if(MemWrite)
		ram[daddr] <= ddata_w;
	end
	// lectura sincrona 
	always @(posedge CLK)
	begin
		if(MemRead)
		ddata_r <= ram[daddr];
	end
	 	

	assert property (@(posedge CLK) MemWrite |=>  (ram[$past(daddr, 1)] == $past(ddata_w, 1))) else  $error ("No escribe");
	
endmodule