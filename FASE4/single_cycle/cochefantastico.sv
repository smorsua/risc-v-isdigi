
`include "../Shared/MUX.sv"
`ifndef SINGLE_CYCLE_GUARD
`define SINGLE_CYCLE_GUARD

`include "../Shared/MUX.sv"
`include "../Shared/ALU/ALU.sv"
`include "../Shared/ALU/operation_type.sv"
`include "../Shared/Control/ALU_CONTROL.sv"
`include "../Shared/Control/CONTROL.sv"
`include "../Shared/Control/IMMEDIATE_GENERATOR.sv"
`include "../Shared/Control/instruction_type.sv"

`include "./banco_registros/banco_registros_unregistered.sv"
`include "./memories/ram_unregistered.sv"
`include "./memories/rom_unregistered.sv"

module cochefantastico
#(parameter DATA_SIZE = 32, parameter ADDR_SIZE = 10)(
    input                   CLK,
    input                   RESET_N


);

wire [DATA_SIZE-1:0]  idata;
wire [ADDR_SIZE-1:0]  iaddr;
wire [ADDR_SIZE-1:0]  daddr;
wire [DATA_SIZE-1:0]  ddata_r;
wire [DATA_SIZE-1:0]  ddata_w;
wire mem_write;
wire mem_read;


wire reg_write_enable;
wire [DATA_SIZE-1:0] reg_write_data;
wire [4:0] write_register;

single_cycle main(CLK, RESET_N, idata, iaddr, daddr, ddata_r, ddata_w, d_rw);
defparam main.ADDR_WIDTH = ADDR_SIZE;
defparam main.SIZE = DATA_SIZE;

wire [DATA_SIZE-1:0]ddata_r_ram;
//wire [DATA_SIZE-1:0]ddata_w;
wire [ADDR_SIZE-1:0] daddr_ram;
wire d_rw_ram;



ram_unregistered ram_unregistered(CLK, daddr_ram, d_rw_ram, ddata_w, ddata_r_ram);
defparam ram_unregistered.addr_width = ADDR_SIZE;
defparam ram_unregistered.data_width = DATA_SIZE;

rom_unregistered rom_unregistered(.iaddr(iaddr), .idata(idata));
defparam rom_unregistered.addr_width = ADDR_SIZE;
defparam rom_unregistered.data_width = DATA_SIZE;
defparam rom_unregistered.file = "./leds_placa.txt" ;


wire d_rw_GPIO;
wire [DATA_SIZE-1:0]  ddata_r_GPIO;
wire [ADDR_SIZE-1:0] daddr_GPIO;

ram_unregistered ram_GPIO(CLK, daddr_GPIO, d_rw_GPIO, ddata_w, ddata_r_GPIO);
defparam ram_GPIO.addr_width = ADDR_SIZE;
defparam ram_GPIO.data_width = DATA_SIZE;


reg addr12_reg;
always @(posedge CLK)
    begin
        addr12_reg<= daddr[9];

    end

////////////////////////////////////INVERSOR(HACIA PLACA)\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
assign d_rw_ram = (daddr[9] == 1'b0)? d_rw:1'b0;
assign d_rw_GPIO = !d_rw_ram;
//////////////////////////////////////////////MUX(HACIA MICRO)\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
wire [DATA_SIZE-1:0] myInput_mem_controller[2];
assign myInput_mem_controller[0] = ddata_r_ram;
assign myInput_mem_controller[1] =  ddata_r_GPIO;
MUX #(.SIZE(DATA_SIZE), .INPUTS(2)) mem_controller (
    .all_inputs(myInput_mem_controller),
    .sel(addr12_reg),
    .result(ddata_r)
);


endmodule

`endif
