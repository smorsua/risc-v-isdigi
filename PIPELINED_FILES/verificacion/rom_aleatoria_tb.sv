`include "if_ram.sv"
`include "if_rom.sv"
`include "../single_cycle/main.sv"
module ram_with_if(if_ram.ram_module bus);
  ram_golden ram(CLK, bus.daddr, bus.d_rw, bus.ddata_w, bus.ddata_r);
  defparam ram.addr_width = 10;
  defparam ram.data_width = 32;
endmodule

module rom_aleatoria_tb ();
  // Parameters
  localparam  d_width = 32;
  localparam  mem_depth = 1024;
  localparam a_width=$clog2(mem_depth);
	localparam T = 10;

  
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




  golden main_circuit(
      .CLK(CLK),
      .RESET_N(RESET_N),
      .idata(interface_rom.main_circuit.idata),
      .iaddr(interface_rom.main_circuit.iaddr),
      .daddr(interface_ram.main_circuit.daddr),
      .ddata_r(interface_ram.main_circuit.ddata_r),
      .ddata_w(interface_ram.main_circuit.ddata_w),
      .d_rw(interface_ram.main_circuit.d_rw)
  );

ram_with_if ram_con_interfaz(interface_ram.ram_module);
endmodule