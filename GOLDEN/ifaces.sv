interface ifaces( input CLK, input RESET_N, input CLEAR);
//Del interfaz tu defines siempre las señales más globales, las que no dependen del diseño

parameter data_width = 32; // data width in bits
parameter addr_width = 10; // address width in bits

// interface signals
// Aquí definimos todas las señales que vamos a utilizar.
logic d_rw_golden ;
logic  [(data_width-1):0] ddata_w, ddata_w_golden ;
logic [(addr_width-1):0] daddr, daddr_golden ;
logic  [(data_width-1):0] ddata_r, ddata_r_golden ;
logic [(addr_width-1):0] iaddr, iaddr_golden ;
logic  [(data_width-1):0] idata, idata_golden ;
logic MemRead, MemWrite;

/*--------------------------------------
* Este modport está principalmente usado para el muestreo de las señales, tu cuando muestreas básicamente estás
* sacando los valores del diseño.
----------------------------------------*/
modport monitor(
input CLK,      input RESET_N,
                input d_rw_golden,
input ddata_w,  input ddata_w_golden,
input daddr,    input daddr_golden,
input ddata_r,  input ddata_r_golden,
input iaddr,    input iaddr_golden,
input idata,    input idata_golden,
input MemRead,
input MemWrite,
input CLEAR
);

/*--------------------------------------
*Este modport es el de testeo, que es lo que te he dicho antes que serviría para modificar tu las señales,
* la señal que quieres modificar tendría que ser definida como output y no cmoo input
----------------------------------------*/
modport testeo(
                input d_rw_golden,
input ddata_w,  input ddata_w_golden,
input daddr,    input daddr_golden,
input ddata_r,  input ddata_r_golden,
input iaddr,    input iaddr_golden,
input idata,    input idata_golden,
input MemRead,
input MemWrite,
input CLEAR
);


/*--------------------------------------
* Aquí definimos otros dos modports que son básicamente los que respetan las entradas y salidas del diseño, tanto
* pipelined como golden model. ya está, sería lo mismo coger y hacelro directamente pero ya que haces interfaces
*
----------------------------------------*/
modport duv(
input CLK,
input RESET_N,
input CLEAR,
output ddata_w,
output daddr,
output ddata_r,
output iaddr,
output idata,
output MemRead,
output MemWrite
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
output ddata_r_golden,
output iaddr_golden,
output idata_golden

);


endinterface