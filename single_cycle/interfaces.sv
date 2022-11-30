//`timescale 1ns/1ps
interface test_if #(parameter SIZE = 32) (input bit clk, input bit rst_n);
    logic start;
    logic signed [SIZE-1:0] numerador;
    logic signed [SIZE-1:0] denominador;
    logic signed [SIZE-1:0] cociente;
    logic signed [SIZE-1:0] resto;
    logic done;

    clocking monitor_cb @(posedge clk);
        default input #3ns;
        input start;
        input rst_n;
        input numerador;
        input denominador;
        input cociente;
        input resto;
        input done;
    endclocking : monitor_cb;

    clocking stimulus_cb @(posedge clk);
        default input #3ns output #3ns;
        input done;
        output start;
        output rst_n;
        output numerador;
        output denominador;
    endclocking : stimulus_cb;

    modport monitor(clocking monitor_cb);
    modport stimulus(clocking stimulus_cb);

    modport duv (
        input   clk,
        input   start,
        input   rst_n,
        input   numerador,
        input   denominador,
        output  cociente,
        output  resto,
        output  done
    );
endinterface:test_if