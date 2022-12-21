module ram_golden
#(parameter data_width=32, parameter addr_width=10)
(
	input CLK,
	input  [(addr_width-1):0] daddr,
	input d_rw, 
    input  [(data_width-1):0] ddata_w,
	output reg [(data_width-1):0] ddata_r
);
	reg [data_width-1:0] ram[2**addr_width-1:0];

	integer i;
	initial begin
		for(i=0; i < 2 ** addr_width; i++) begin
			ram[i] = 'b0;
		end
	end

    always @(posedge CLK)
    begin
	 if(d_rw)
		ram[daddr] <= ddata_w;
	end

	assign 	ddata_r = ram[daddr];

	assert property (@(posedge CLK) d_rw |=>  (ram[$past(daddr, 1)] == $past(ddata_w, 1))) else  $error ("No escribe");
endmodule