
module tb_ifaces();
parameter addr_width = 10; 
parameter data_width = 32;

logic CLK, RESET_N;

// inicializamos la interfaz
ifaces iface(.CLK(CLK), .RESET_N(RESET_N));


// "INICIALIZO" los dos cores primero el pipelined y el golden 
//DUV
// Aquí tenemos un problema y es que realmente, no podemos conectar directamente con interfaces el bicho este
// porque todo esta conectado, así que voy a tener que realizar las conexiones y luego hacer asignacions sino esto
// no va a funcionar.
// Defino todos los cables que hay que usar
logic [addr_width-1:0] iaddr, daddr;
logic [data_width-1:0] idata, ddata_w, ddata_r;
logic MemWrite, MemRead;

ram ram(.CLK(iface.duv.CLK), .daddr(daddr), .MemWrite(MemWrite), .MemRead(MemRead), .ddata_w(ddata_w), .ddata_r(ddata_r));
defparam ram.addr_width = addr_width;
defparam ram.data_width = data_width;

rom rom(.CLK(iface.duv.CLK), .iaddr(iaddr), .idata(idata));
defparam rom.addr_width = addr_width;
defparam rom.data_width = data_width;
defparam rom.file = "fibonacci.txt" ;

main DUV (.CLK(iface.duv.CLK), .RESET_N(iface.duv.RESET_N), .CLEAR(iface.duv.CLEAR), 
          .idata(idata), .iaddr(iaddr), 
          .daddr(daddr), .ddata_r(ddata_r), 
          .ddata_w(ddata_w), .MemWrite(MemWrite), 
          .MemRead(MemRead));
defparam main.ADDR_SIZE = addr_width;
defparam main.DATA_SIZE = data_width;
//asignacion de las salidas del interfaz, a conexiones entre el core y la memoria
assign iface.duv.iaddr = iaddr;
assign iface.duv.idata = idata;
assign iface.duv.daddr = daddr;
assign iface.duv.ddata_r = ddata_r;
assign iface.duv.ddata_w = ddata_w;
assign iface.duv.MemWrite = MemWrite;
assign iface.duv.MemRead = MemRead;

//GOLDEN MODEL 
logic [addr_width-1:0] iaddr_golden, daddr_golden;
logic [data_width-1:0] idata_golden, ddata_golden, ddata_r_golden;
logic MemWrite_golden, MemRead_golden;

ram_golden ram(.CLK(iface.golden.CLK), .daddr( daddr_golden), .MemWrite( MemWrite_golden), .MemRead( MemRead_golden), .ddata_w( ddata_golden), .ddata_r( ddata_r_golden));
defparam ram.addr_width = addr_width;
defparam ram.data_width = data_width;

rom_golden rom(.CLK(iface.golden.CLK), .iaddr( iaddr_golden), .idata( idata_golden));
defparam rom.addr_width = addr_width;
defparam rom.data_width = data_width;
defparam rom.file = "fibonacci.txt" ;

golden golden (.CLK(iface.golden.CLK), .RESET_N(iface.golden.RESET_N), .CLEAR(iface.golden.CLEAR), 
          .idata( idata_golden), .iaddr( iaddr_golden), 
          .daddr( daddr_golden), .ddata_r( ddata_r_golden), 
          .ddata_w( ddata_golden), .MemWrite( MemWrite_golden), 
          .MemRead( MemRead_golden));
defparam main.ADDR_SIZE = addr_width;
defparam main.DATA_SIZE = data_width;
//asignacion de las salidas del interfaz, a conexiones entre el core y la memoria
assign iface.golden.iaddr_golden = iaddr_golden;
assign iface.golden.idata_golden = idata_golden;
assign iface.golden.daddr_golden = daddr_golden;
assign iface.golden.ddata_r_golden = ddata_r_golden;
assign iface.golden.ddata_w_golden = ddata_golden;
assign iface.golden.MemWrite_golden = MemWrite_golden;
assign iface.golden.MemRead_golden = MemRead_golden;

endmodule