module rom_aleatoria_tb ();

  // Parameters
  localparam  d_width = 32;
  localparam  mem_depth = 1024;
  localparam a_width=$clog2(mem_depth);
  // Ports
  reg [a_width-1:0] address;
  reg clk;
  logic [d_width-1:0] dato;

utilidades_verificacion::instruction_box m1=new();

if_rom interfaz_rom ();

top_duv    rom_aleatoria_dut (.bus(interfaz_rom) );

estimulos  rom_aleatoria_estimulos (.testar_ports(interfaz_rom), .monitorizar_ports(interfaz_rom));


endmodule