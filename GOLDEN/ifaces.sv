`ifndef IFACES_GUARD
`define IFACES_GUARD
interface ifaces(input CLK, input RESET_N, input CLEAR);
//Del interfaz tu defines siempre las señales más globales, las que no dependen del diseño

parameter data_width = 32; // data width in bits
parameter addr_width = 10; // address width in bits

// interface signals
// Aquí definimos todas las señales que vamos a utilizar.
logic                   d_rw_golden ;
logic [data_width-1:0]  ddata_w, ddata_w_golden ;
logic [addr_width-1:0]  daddr, daddr_golden ;
logic [data_width-1:0]  ddata_r, ddata_r_golden ;
logic [addr_width-1:0]  iaddr, iaddr_golden ;
logic [data_width-1:0]  idata, idata_golden ;
logic                   MemRead, MemWrite;
logic [data_width-1:0]  reg_write_data, reg_write_data_golden;
logic reg_write_enable, reg_write_enable_golden;
logic [4:0] write_register_golden, write_register;
/*--------------------------------------
* Este modport está principalmente usado para el muestreo de las señales, tu cuando muestreas básicamente estás
* sacando los valores del diseño.
----------------------------------------*/

 clocking monitor_cb @(posedge CLK);
    default input #3ns;
    input CLK;
    input RESET_N;
    input CLEAR;
    input d_rw_golden;
    input ddata_w;
    input ddata_w_golden;
    input daddr;
    input daddr_golden;
    input ddata_r;
    input ddata_r_golden;
    input iaddr;
    input iaddr_golden;
    input idata;
    input idata_golden;
    input MemRead;
    input MemWrite;
    input reg_write_data;
    input reg_write_data_golden;
    input reg_write_enable;
    input reg_write_enable_golden;
    input write_register_golden;
    input write_register;
    endclocking : monitor_cb;

modport monitor(clocking monitor_cb);

/*--------------------------------------
*Este modport es el de testeo, que es lo que te he dicho antes que serviría para modificar tu las señales,
* la señal que quieres modificar tendría que ser definida como output y no cmoo input
----------------------------------------*/
modport testeo(
    input d_rw_golden,
    input ddata_w,
    input ddata_w_golden,
    input daddr,
    input daddr_golden,
    input ddata_r,
    input ddata_r_golden,
    input iaddr,
    input iaddr_golden,
    input idata,
    input idata_golden,
    input MemRead,
    input MemWrite,
    input CLEAR
);


/*--------------------------------------
* Aquí definimos otros dos modports que son básicamente los que respetan las entradas y salidas del diseño, tanto
* pipelined como golden model. ya está, sería lo mismo coger y hacelro directamente pero ya que haces interfaces
*
----------------------------------------*/
modport pipelined(
    input CLK,
    input RESET_N,
    input CLEAR,
    output iaddr,
    input idata,
    output daddr,
    input ddata_r,
    output ddata_w,
    output MemRead,
    output MemWrite,
    output reg_write_data,
    output reg_write_enable,
    output write_register
);

/*--------------------------------------
*Este es el del golden model.
----------------------------------------*/

modport golden(
    input CLK,
    input RESET_N,
    output d_rw_golden,
    output ddata_w_golden,
    output daddr_golden,
    input ddata_r_golden,
    output iaddr_golden,
    input idata_golden,
    output reg_write_data_golden,
    output reg_write_enable_golden,
    output write_register_golden
);

modport memories(
    input CLK,
    input RESET_N,
    input CLEAR,
    input iaddr,
    input iaddr_golden,
    output idata,
    output idata_golden,
    input daddr,
    input daddr_golden,
    input ddata_w,
    input ddata_w_golden,
    output ddata_r,
    output ddata_r_golden,
    input MemRead,
    input MemWrite,
    input d_rw_golden
);


endinterface
`endif