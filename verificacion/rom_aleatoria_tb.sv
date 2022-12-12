`include "if_ram.sv"
`include "if_rom.sv"
`include "../single_cycle/main.sv"
module ram_with_if(if_ram.ram_module bus);
  RAM ram(CLK, bus.address, bus.enable, bus.dato_entrada, bus.address, bus.dato_salida);
  defparam ram.addr_width = 10;
  defparam ram.data_width = 32;
endmodule

module rom_aleatoria_tb ();
  // Parameters
  localparam  d_width = 32;
  localparam  mem_depth = 1024;
  localparam a_width=$clog2(mem_depth);
	localparam T = 10;

  // Ports
  reg [a_width-1:0] address;
  reg clk;
  logic [d_width-1:0] dato;

  logic CLK;
  logic RESET_N;

  initial
	begin
		CLK = 0;
		forever  #(T/2) CLK=!CLK;
	end 

	initial begin
		RESET_N = 0;
		#(T)
		RESET_N = 1;
	end

  utilidades_verificacion::instruction_box m1=new();

  if_rom interface_rom();
  if_ram interface_ram();

  top_duv rom_aleatoria_dut(.bus(interface_rom.duv));

  estimulos rom_aleatoria_estimulos(.monitorizar_ports(interface_rom.monitorizar));




  main main_circuit(
      .CLK(CLK),
      .RESET_N(RESET_N),
      .Q_ROM(interface_rom.main_circuit.dato),
      .ADDR_ROM(interface_rom.main_circuit.address),
      .ADDR_RAM(interface_ram.main_circuit.address),
      .Q_RAM(interface_ram.main_circuit.dato_salida),
      .Q_W(interface_ram.main_circuit.dato_entrada),
      .ENABLE_W(interface_ram.main_circuit.enable)
  );

ram_with_if ram_con_interfaz(interface_ram.ram_module);
endmodule