program  estimulos (if_rom.testar testar_ports, if_rom.monitorizar monitorizar_ports);

 utilidades_verificacion::RCSG_RISCV generar_instrucciones;
 utilidades_verificacion::covergroups_RISCV monitorizar_instrucciones;

logic [31:0] instruccion_random;

  initial 
    begin
      generar_instrucciones=new;
      monitorizar_instrucciones=new(monitorizar_ports);

      # 50;

      $display("probando r_format" );
      generar_instrucciones.R_format.constraint_mode(1);
      generar_instrucciones.I_format.constraint_mode(0);
      prueba_random_r_format();
      $display("Fin R_format :: time is %0t",$time); 
      generar_instrucciones.R_format.constraint_mode(0);
      generar_instrucciones.I_format.constraint_mode(1);
      prueba_random_i_format();
      $stop;
      $writememh("salida_random.txt", rom_aleatoria_tb.rom_aleatoria_dut.duv.tipos_paquete);      
      $finish;

  end

task prueba_random_r_format;
  begin
      assert (generar_instrucciones.randomize()) else    $fatal("randomization failed");   
      rom_aleatoria_tb.m1.put(generar_instrucciones.valor);
      testar_ports.address='0; 
      #0 monitorizar_instrucciones.instrucciones.sample();  
      while ( monitorizar_instrucciones.instrucciones.rformat.get_coverage()<100)
	begin
	   # 100 ;
	   assert (generar_instrucciones.randomize()) else    $fatal("randomization failed");     
     	   rom_aleatoria_tb.m1.put(generar_instrucciones.valor);
	   testar_ports.address= testar_ports.address +1;
           #0 monitorizar_instrucciones.instrucciones.sample();
        end
  end
endtask

task prueba_random_i_format;
  begin
      assert (generar_instrucciones.randomize()) else    $fatal("randomization failed");   
      rom_aleatoria_tb.m1.put(generar_instrucciones.valor);
      testar_ports.address= testar_ports.address +1 ;
      #0 monitorizar_instrucciones.instrucciones.sample();  
      while ( monitorizar_instrucciones.instrucciones.iformat.get_coverage()<100)
	begin
	   # 100 ;
	   assert (generar_instrucciones.randomize()) else    $fatal("randomization failed");     
     	   rom_aleatoria_tb.m1.put(generar_instrucciones.valor);
	   testar_ports.address= testar_ports.address +1;
           #0 monitorizar_instrucciones.instrucciones.sample();
        end
  end
endtask
endprogram