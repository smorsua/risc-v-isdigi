`timescale 1ns/1ps
interface test_if #(parameter SIZE = 32, parameter ADDR_WIDTH = 10) (input bit clk, input bit rst_n);
// Es necesario adaptar esto para los estímulos que tendría nuestro top, en este caso
    
    logic [SIZE-1:0] Q_ROM;
    logic [ADDR_WIDTH-1:0] ADDR_ROM;
    logic [ADDR_WIDTH-1:0] ADDR_RAM;
    logic [SIZE-1:0] Q_RAM;
    logic [SIZE-1:0] Q_W;
    logic ENABLE_W;

    clocking monitor_cb @(posedge clk);
        default input #3ns;
        input [SIZE-1:0] Q_ROM;
        input [ADDR_WIDTH-1:0] ADDR_ROM;
        input [ADDR_WIDTH-1:0] ADDR_RAM;
        input [SIZE-1:0] Q_RAM;
        input [SIZE-1:0] Q_W;
        input ENABLE_W;
    endclocking : monitor_cb;

    clocking stimulus_cb @(posedge clk);
        default input #3ns output #3ns;
        input [ADDR_WIDTH-1:0] ADDR_ROM,
        input [ADDR_WIDTH-1:0] ADDR_RAM,
        input [SIZE-1:0] Q_W,
        input ENABLE_W,
        output [SIZE-1:0] Q_ROM,
        output [SIZE-1:0] Q_RAM
    endclocking : stimulus_cb;

    modport monitor(clocking monitor_cb);
    modport stimulus(clocking stimulus_cb);

    modport duv (
        input clk, 
        input rst_n,
        input [SIZE-1:0] Q_ROM,
        input [SIZE-1:0] Q_RAM,
        output [ADDR_WIDTH-1:0] ADDR_ROM,
        output [ADDR_WIDTH-1:0] ADDR_RAM,
        output [SIZE-1:0] Q_W,
        output ENABLE_W
    );
endinterface:test_if