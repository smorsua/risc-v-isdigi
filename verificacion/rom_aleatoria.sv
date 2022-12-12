module rom_aleatoria (address,dout);
parameter d_width = 32;
parameter mem_depth = 1000;
localparam a_width=$clog2(mem_depth);
input [a_width-1:0] address;
output logic [d_width-1:0] dout;

logic [d_width-1:0] tipos_paquete[logic[a_width-1:0]]; // tipo de paquete es 16 bits

logic [d_width-1:0] temp;
logic [a_width-1:0] temp_address;

always @(address) begin
  temp_address = address;
  if (!tipos_paquete.exists(temp_address))
    begin
      rom_aleatoria_tb.m1.get(temp);
      tipos_paquete[temp_address]=temp;	
      dout=tipos_paquete[temp_address];
    end
  else
    begin
      rom_aleatoria_tb.m1.get(temp);
      dout=tipos_paquete[temp_address];
   end
end


endmodule
