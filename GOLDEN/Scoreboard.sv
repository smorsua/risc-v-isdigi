`ifndef SCOREBOARD_GUARD
`define SCOREBOARD_GUARD
// CREANDO UNA CLASE ENCARGADA DE COMPRAR LOS RESULTADOS, PRIMERO COMPARAMOS CON EL RESULTADO DE LA RAM Y EL BANCO DE REGISTROS
class Scoreboard;
logic [31:0] register_write_data[$];
logic [31:0] ram_write_data[$];

virtual ifaces.monitor scoreboard_if;
logic [31:0] register_write_data_golden;
function new (
    virtual ifaces.monitor scoreboard, 
    logic [31:0] register_write_data_golden);
    begin
        this.scoreboard_if = scoreboard;
        this.register_write_data_golden = register_write_data_golden;
    end
endfunction

//aquí hay que realizar las tasks, para conseguir comparar las señales del golden model y el
//resultado del pipelined

//TASK PARA COMPROBAR LA RAM

    task monitor_input();
    begin
        while(1) begin
            @(scoreboard_if.iaddr_golden) begin
                register_write_data.push_back(register_write_data_golden);     
                ram_write_data.push_back(scoreboard_if.ddata_w_golden);     
            end
        end
    end
    endtask

	// task comprueba_RAM;
	// 	reg [31:0] data_golden;
	// 	begin
	// 		while(1)
	// 		begin
	// 		@(negedge scoreboard_if.CLK)
	// 		if (scoreboard_if.d_rw_golden ==1'b1 && scoreboard_if.RESET_N)
	// 		begin
	// 		data_golden = scoreboard_if.ddata_w_golden;
	// 		assert (data_golden == (##2 scoreboard_if.ddata_w)) else $error("El valor escrito en la RAM es incorrecto");
	// 		end
	// 		end
	// 	end

	// endtask

	// TASK PARA COMPROBAR EL BANCO REGISTROS

// task comprueba_banco;
// 	reg [31:0] data_golden;
// 	begin
// 		while(1)
// 		begin
// 		@(negedge scoreboard_if.CLK)
// 		if (scoreboard_if.RegWrite_golden == 1'b1 && scoreboard_if.RESET_N)
// 		begin
// 		data_golden = scoreboard_if.writeData_golden;
// 		assert (data_golden == (##5 scoreboard_if.writeData)) else $error("El valor escrito en los  Banco de Registros es incorrecto");
// 		end
// 		end
// 		end
// endtask

endclass
    //debería usar interfaces para comprobar a cada ciclo de reloj la ram y el banco de registros

`endif



