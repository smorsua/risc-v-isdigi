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
      activate_constraints_RISBU(5'b10000);
      prueba_random_r_format();
      $display("Fin R_format :: time is %0t",$time); 

      activate_constraints_RISBU(5'b01000);
      prueba_random_i_format();
      $display("Fin I_format :: time is %0t",$time); 

      activate_constraints_RISBU(5'b00100);
      prueba_random_s_format();
      $display("Fin S_format :: time is %0t",$time); 

      activate_constraints_RISBU(5'b00010);
      prueba_random_b_format();
      $display("Fin B_format :: time is %0t",$time); 

      activate_constraints_RISBU(5'b00001);
      prueba_random_u_format();
      $display("Fin U_format :: time is %0t",$time); 

  
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

task prueba_random_s_format;
  begin
      assert (generar_instrucciones.randomize()) else    $fatal("randomization failed");   
      rom_aleatoria_tb.m1.put(generar_instrucciones.valor);
      testar_ports.address= testar_ports.address +1 ;
      #0 monitorizar_instrucciones.instrucciones.sample();  
      while ( monitorizar_instrucciones.instrucciones.sformat.get_coverage()<100)
	begin
	   # 100 ;
	   assert (generar_instrucciones.randomize()) else    $fatal("randomization failed");     
     	   rom_aleatoria_tb.m1.put(generar_instrucciones.valor);
	   testar_ports.address= testar_ports.address +1;
           #0 monitorizar_instrucciones.instrucciones.sample();
        end
  end
endtask

task prueba_random_b_format;
  begin
      assert (generar_instrucciones.randomize()) else    $fatal("randomization failed");   
      rom_aleatoria_tb.m1.put(generar_instrucciones.valor);
      testar_ports.address= testar_ports.address +1 ;
      #0 monitorizar_instrucciones.instrucciones.sample();  
      while ( monitorizar_instrucciones.instrucciones.bformat.get_coverage()<100)
	begin
	   # 100 ;
	   assert (generar_instrucciones.randomize()) else    $fatal("randomization failed");     
     	   rom_aleatoria_tb.m1.put(generar_instrucciones.valor);
	   testar_ports.address= testar_ports.address +1;
           #0 monitorizar_instrucciones.instrucciones.sample();
        end
  end

endtask

task prueba_random_u_format;
  begin
      assert (generar_instrucciones.randomize()) else    $fatal("randomization failed");   
      rom_aleatoria_tb.m1.put(generar_instrucciones.valor);
      testar_ports.address= testar_ports.address +1 ;
      #0 monitorizar_instrucciones.instrucciones.sample();  
      while ( monitorizar_instrucciones.instrucciones.uformat.get_coverage()<100)
	begin
	   # 100 ;
	   assert (generar_instrucciones.randomize()) else    $fatal("randomization failed");     
     	   rom_aleatoria_tb.m1.put(generar_instrucciones.valor);
	   testar_ports.address= testar_ports.address +1;
           #0 monitorizar_instrucciones.instrucciones.sample();
        end
  end
endtask


task activate_constraints_RISBU(input [4:0] activate );
  // rsbiu
  generar_instrucciones.R_format.constraint_mode(activate[4]);
  generar_instrucciones.I_format.constraint_mode(activate[1]);
  generar_instrucciones.S_format.constraint_mode(activate[3]);
  generar_instrucciones.B_format.constraint_mode(activate[2]);
  generar_instrucciones.U_format.constraint_mode(activate[0]);
endtask

endprogram