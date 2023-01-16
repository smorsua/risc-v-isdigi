`ifndef PIPELINED_GUARD
`define PIPELINED_GUARD

`include "../Shared/MUX.sv"
`include "../Shared/ALU/ALU.sv"
`include "../Shared/ALU/operation_type.sv"
`include "../Shared/Control/ALU_CONTROL.sv"
`include "../Shared/Control/CONTROL.sv"
`include "../Shared/Control/IMMEDIATE_GENERATOR.sv"
`include "../Shared/Control/instruction_type.sv"

`include "./banco_registros/banco_registros_registered.sv"
`include "./memories/ram_registered.sv"
`include "./memories/rom_registered.sv"

`include "./pipelined_registers/IF_ID_REG.sv"
`include "./pipelined_registers/ID_EX_REG.sv"
`include "./pipelined_registers/EX_MEM_REG.sv"
`include "./pipelined_registers/MEM_WB_REG.sv"

`include "./risk_detection/hazard_detection.sv"

module cochefantastico
#(parameter DATA_SIZE = 32, parameter ADDR_SIZE = 10)(
    input                   CLK,
    input                   RESET_N,
    input                   CLEAR

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

pipelined pipelined(CLK, RESET_N,CLEAR, idata, iaddr, daddr, ddata_r, ddata_w, mem_write, mem_read,reg_write_data, reg_write_enable, write_register);
defparam pipelined.ADDR_SIZE = ADDR_SIZE;
defparam pipelined.DATA_SIZE = DATA_SIZE;

wire [DATA_SIZE-1:0]ddata_r_ram;
wire [DATA_SIZE-1:0]ddata_w_ram;
wire [ADDR_SIZE-1:0] daddr_ram;
wire mem_read_ram;
wire mem_write_ram;
ram_registered ram_registered(CLK, daddr_ram, mem_write_ram, mem_read_ram, ddata_w_ram, ddata_r_ram);
defparam ram_registered.addr_width = ADDR_SIZE;
defparam ram_registered.data_width = DATA_SIZE;

rom_registered rom_registered(.CLK(CLK), .iaddr(iaddr), .idata(idata));
defparam rom_registered.addr_width = ADDR_SIZE;
defparam rom_registered.data_width = DATA_SIZE;
defparam rom_registered.file = "./leds_placa.txt" ;

wire enable_GPIO; //ENABLE DE ESCRITURA
wire mem_read_GPIO; //ENABLE DE LECTURA
wire [DATA_SIZE-1:0] ddata_w_GPIO, ddata_r_GPIO;
wire [ADDR_SIZE-1:0] daddr_GPIO;
ram_registered ram_GPIO(CLK, daddr_GPIO, enable_GPIO, mem_read_GPIO, ddata_w_GPIO, ddata_r_GPIO);
defparam ram_GPIO.addr_width = ADDR_SIZE;
defparam ram_GPIO.data_width = DATA_SIZE;

reg addr12_reg;
always @(posedge CLK)
    begin
        addr12_reg<= daddr[12];

    end

////////////////////////////////////INVERSOR(HACIA PLACA)\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
assign {mem_write_ram,mem_read_ram} = (daddr[12] == 1'b0)? {mem_write,mem_read}:1'b0;
assign {mem_write_GPIO,mem_read_GPIO} = (daddr[12] == 1'b1)? {mem_write,mem_read}:1'b0;
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
