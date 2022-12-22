interface ifaces( input CLK, input RESET_N);

parameter data_width = 32; // data width in bits
parameter addr_width = 10; // address width in bits

// interface signals
logic CLEAR;
logic d_rw, d_rw_golden ;
logic  [(data_width-1):0] ddata_w, ddata_w_golden ;
logic [(addr_width-1):0] daddr, daddr_golden ;
logic  [(data_width-1):0] ddata_r, ddata_r_golden ;
logic [(addr_width-1):0] iaddr, iaddr_golden ;
logic  [(data_width-1):0] idata, idata_golden ;

// modport de monitoreo principalmente usada para el muestreo de las señales y
//  la comprobación de los resultados con un golden model o lo q sea
modport monitor(
input CLK,      input RESET_N,
input d_rw,     input d_rw_golden,
input ddata_w,  input ddata_w_golden,
input daddr,    input daddr_golden,
input ddata_r,  input ddata_r_golden,
input iaddr,    input iaddr_golden,
input idata,    input idata_golden,
input CLEAR
);

// mopdport de testeo para la generación de señales a tu gusto 
//en esto caso no lo estamos utilizando, ya que deberían ser output del modport las señales que vamos a modificar
modport testeo(
input d_rw,     input d_rw_golden,
input ddata_w,  input ddata_w_golden,
input daddr,    input daddr_golden,
input ddata_r,  input ddata_r_golden,
input iaddr,    input iaddr_golden,
input idata,    input idata_golden,
input CLEAR
);

modport duv(
input CLK, 
input RESET_N,    
output d_rw,    
output ddata_w, 
output daddr,   
output ddata_r, 
output iaddr,   
output idata,
output CLEAR   

);

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