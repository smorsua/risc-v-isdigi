module rom_aleatoria (address,dout);
parameter d_width = 32;
parameter mem_depth = 1024;
localparam a_width=$clog2(mem_depth);
input [a_width-1:0] address;
output logic [d_width-1:0] dout;
 
logic [d_width-1:0] mem[mem_depth-1:0] ; 
 
// `ifndef debug_aleatorio 
 
// initial
//     $readmemh("contenido_fijo.dat", mem); 
// assign dout = mem[address];

// `else 

logic [31:0] tipos_paquete[logic [9:0] ]; // tipo de paquete es 16 bits

logic [31:0] temp;
always @(address)
if (!tipos_paquete.exists(address))
  begin
    rom_aleatoria_tb.m1.get(temp);
    tipos_paquete[address]=temp;	
    dout=tipos_paquete[address];
  end
else
   begin
    rom_aleatoria_tb.m1.get(temp);
    dout=tipos_paquete[address];
   end

// `endif

endmodule
