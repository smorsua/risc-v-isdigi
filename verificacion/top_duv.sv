module top_duv( if_rom.duv bus);

rom_aleatoria #(.d_width(32), .mem_depth(1024)) duv
(.iaddr(bus.iaddr),
.idata(bus.idata));

endmodule
