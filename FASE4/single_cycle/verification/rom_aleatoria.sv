module rom_aleatoria (iaddr,idata);
parameter d_width = 32;
parameter mem_depth = 1000;
localparam a_width=$clog2(mem_depth);
input [a_width-1:0] iaddr;
output logic [d_width-1:0] idata;

logic [d_width-1:0] tipos_paquete[logic[a_width-1:0]]; // tipo de paquete es 16 bits

logic [d_width-1:0] temp;
logic [a_width-1:0] temp_iaddr;

always @(iaddr) begin
  temp_iaddr = iaddr;
  if (!tipos_paquete.exists(temp_iaddr))
    begin
      rom_aleatoria_tb.m1.get(temp);
      tipos_paquete[temp_iaddr]=temp;	
      idata=tipos_paquete[temp_iaddr];
    end
  else
    begin
      rom_aleatoria_tb.m1.get(temp);
      idata=tipos_paquete[temp_iaddr];
   end
end


endmodule
