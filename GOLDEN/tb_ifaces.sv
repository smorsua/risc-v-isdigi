
`timescale 1ns/1ps
module tb_ifaces();
parameter addr_width = 10; 
parameter data_width = 32;

localparam T = 20; 

logic CLK, RESET_N, CLEAR;

// inicializamos la interfaz
ifaces iface(.CLK(CLK), .RESET_N(RESET_N), .CLEAR(CLEAR));



/*--------------------------------------------------------------------------------
 *  Pipelined
 *-------------------------------------------------------------------------------*/

// "INICIALIZO" los dos cores primero el pipelined y el golden 
//DUV
// Aquí tenemos un problema y es que realmente, no podemos conectar directamente con interfaces el bicho este
// porque todo esta conectado, así que voy a tener que realizar las conexiones y luego hacer asignacions sino esto
// no va a funcionar.
// Defino todos los cables que hay que usar
logic [addr_width-1:0] iaddr, daddr;
logic [data_width-1:0] idata, ddata_w, ddata_r;
logic MemWrite, MemRead;

ram ram(.CLK(CLK), .daddr(daddr), .MemWrite(MemWrite), .MemRead(MemRead), .ddata_w(ddata_w), .ddata_r(ddata_r));
defparam ram.addr_width = addr_width;
defparam ram.data_width = data_width;

rom rom(.CLK(CLK), .iaddr(iaddr), .idata(idata));
defparam rom.addr_width = addr_width;
defparam rom.data_width = data_width;
defparam rom.file = "fibonacci.txt" ;

main DUV (.CLK(CLK), .RESET_N(RESET_N), .CLEAR(CLEAR), 
          .idata(idata), .iaddr(iaddr), 
          .daddr(daddr), .ddata_r(ddata_r), 
          .ddata_w(ddata_w), .mem_write(MemWrite), 
          .mem_read(MemRead));
defparam DUV.ADDR_SIZE = addr_width;
defparam DUV.DATA_SIZE = data_width;
//asignacion de las entradas del interfaz, a conexiones entre el core y la memoria
assign iface.duv.iaddr = iaddr;
assign iface.duv.idata = idata;
assign iface.duv.daddr = daddr;
assign iface.duv.ddata_r = ddata_r;
assign iface.duv.ddata_w = ddata_w;
assign iface.duv.MemWrite = MemWrite;
assign iface.duv.MemRead = MemRead;

/*--------------------------------------------------------------------------------
 *  Golden Model
 *-------------------------------------------------------------------------------*/
logic d_rw_golden; 
logic [addr_width-1:0] iaddr_golden, daddr_golden;
logic [data_width-1:0] idata_golden, ddata_golden, ddata_r_golden;
ram_golden ram_golden(.CLK(CLK), .d_rw(d_rw_golden), .daddr( daddr_golden), .ddata_w( ddata_golden), .ddata_r( ddata_r_golden));
defparam ram_golden.addr_width = addr_width;
defparam ram_golden.data_width = data_width;

rom_golden rom_golden(.iaddr( iaddr_golden), .idata( idata_golden));
defparam rom_golden.addr_width = addr_width;
defparam rom_golden.data_width = data_width;
defparam rom_golden.file = "fibonacci.txt" ;

golden golden (.CLK(CLK), .RESET_N(RESET_N),
          .idata( idata_golden), .iaddr( iaddr_golden), 
          .daddr( daddr_golden), .ddata_r( ddata_r_golden), 
          .ddata_w( ddata_golden), .d_rw(d_rw_golden));
defparam golden.ADDR_WIDTH = addr_width;
defparam golden.SIZE = data_width;
//asignacion de las salidas del interfaz, a conexiones entre el core y la memoria
assign iface.golden.iaddr_golden = iaddr_golden;
assign iface.golden.idata_golden = idata_golden;
assign iface.golden.daddr_golden = daddr_golden;
assign iface.golden.ddata_r_golden = ddata_r_golden;
assign iface.golden.ddata_w_golden = ddata_golden;
assign iface.golden.d_rw_golden = d_rw_golden;


initial
begin
	CLK = 0;
	forever  #(T/2) CLK = ~CLK;
end

initial
    begin
        RESET_N = 0;
        CLEAR = 1;
		    #(T/2)
		RESET_N = 1;
        CLEAR = 0;
        #(T*500);
        $stop;

    end


endmodule