// CREANDO UNA CLASE ENCARGADA DE COMPRAR LOS RESULTADOS, PRIMERO COMPARAMOS CON EL RESULTADO DE LA RAM Y EL BANCO DE REGISTROS.
class compare #(parameter addr_width = 10, parameter data_width = 32);
    logic signed [data_width-1:0] ram [2**addr_width-1:0];
    logic signed [data_width-1:0] ram_golden [2**addr_width-1:0];
    logic signed [data_width-1:0][31:0] banco_registros;
    logic signed  [data_width-1:0][31:0] banco_registros_golden;

    function new(logic signed [data_width-1:0] ram [2**addr_width-1:0], 
                 logic signed [data_width-1:0] rom [2**addr_width-1:0],
                 logic signed [data_width-1:0][31:0] banco_registros,
                 logic signed [data_width-1:0][31:0] banco_registros_golden);
        this.ram = ram;
        this.rom = rom;
        this.banco_registros = banco_registros;
        this.banco_registros_golden = banco_registros_golden;
    endfunction

endclass 

class scoreboard extends compare #(parameter addr_width = 10, parameter data_width = 32);

    function new(logic signed [data_width-1:0] ram [2**addr_width-1:0],
                 logic signed [data_width-1:0] ram_golden [2**addr_width-1:0],
                 logic signed [data_width-1:0][31:0] banco_registros,
                 logic signed [data_width-1:0][31:0] banco_registros_golden);

        super.new(ram, ram_golden, banco_registros, banco_registros_golden);
    endfunction

    //debería usar interfaces para comprobar a cada ciclo de reloj la ram y el banco de registros





