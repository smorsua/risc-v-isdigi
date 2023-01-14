`ifndef SCOREBOARD_GUARD
`define SCOREBOARD_GUARD
// CREANDO UNA CLASE ENCARGADA DE COMPRAR LOS RESULTADOS, PRIMERO COMPARAMOS CON EL RESULTADO DE LA RAM Y EL BANCO DE REGISTROS
class Scoreboard;
logic [31:0] reg_write_data_golden_cola[$];
logic [31:0] ram_write_data_golden_cola[$];

virtual ifaces.monitor scoreboard_if;
function new (
    virtual ifaces.monitor scoreboard);
    begin
        this.scoreboard_if = scoreboard;
    end
endfunction

//aquí hay que realizar las tasks, para conseguir comparar las señales del golden model y el
//resultado del pipelined

//TASK PARA COMPROBAR LA RAM

    task monitor_input();
    begin
        while(1) begin
            @(scoreboard_if.monitor_cb) begin              
                if (scoreboard_if.monitor_cb.reg_write_enable_golden == 1'b1 
                && scoreboard_if.monitor_cb.RESET_N 
                && scoreboard_if.monitor_cb.write_register_golden != 5'b0) begin
                    reg_write_data_golden_cola.push_back(scoreboard_if.monitor_cb.reg_write_data_golden);
                end

                if(scoreboard_if.monitor_cb.d_rw_golden == 1                
                && scoreboard_if.monitor_cb.RESET_N) begin
                    ram_write_data_golden_cola.push_back(scoreboard_if.monitor_cb.ddata_w_golden);                    
                end
            end
        end
    end
    endtask

    task monitor_output();
    begin
        while(1) begin
            @(scoreboard_if.monitor_cb) begin    
                if (scoreboard_if.monitor_cb.reg_write_enable == 1'b1 
                && scoreboard_if.monitor_cb.RESET_N 
                && scoreboard_if.monitor_cb.write_register != 5'b0) begin
                    assert(reg_write_data_golden_cola.pop_front() == scoreboard_if.monitor_cb.reg_write_data) else $display("REGISTER VALUE DOESN'T MATCH");
                end

                if(scoreboard_if.monitor_cb.MemWrite == 1                
                && scoreboard_if.monitor_cb.RESET_N) begin
                    assert(ram_write_data_golden_cola.pop_front() == scoreboard_if.monitor_cb.ddata_w) else $display("RAM VALUE DOESN'T MATCH");     
                end
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



