// CREANDO UNA CLASE ENCARGADA DE COMPRAR LOS RESULTADOS, PRIMERO COMPARAMOS CON EL RESULTADO DE LA RAM Y EL BANCO DE REGISTROS
class scoreboard;

virtual ifaces.monitor scoreboard_if;

function new (virtual ifaces.monitor scoreboard);
    begin
        this.scoreboard_if = scoreboard;
    end
endfunction


//aquí hay que realizar las tasks, para conseguir comparar las señales del golden model y el
//resultado del pipelined





endclass
    //debería usar interfaces para comprobar a cada ciclo de reloj la ram y el banco de registros





