`timescale 1ns/1ps

module alu_test();


localparam SLEEP_TIME = 10;
localparam SIZE = 32;

bit[SIZE-1:0] A, B, RESULT;
bit[3:0] OPERATION;
bit ZERO;

initial begin
    add(10,10);
    sleep();
    sub_task(10,10);
    sleep();
    sub_task(10,5);
    sleep();
    less_than(10,5);
    sleep();
    less_than(0,10);
    sleep();
    greater_or_equal_than(0,10);
    sleep();
    greater_or_equal_than(234,44);
    sleep();
    and_task(0,13413);
    sleep();
    and_task(1,543);
    sleep();
    and_task(8,'hffff);
    sleep();
    or_task(134,41234);
    sleep();
    xnor_task(1243,1243);
    sleep();
    xnor_task(1243,3532);
    sleep();
    left_shift(1,4);
    sleep();
    left_shift(1343,30);
    sleep();
    right_shift(123,4);
    sleep();
    set_input(10,34,432);
    $stop;
end

ALU_golden #(.SIZE(SIZE)) duv(
    .A(A),
    .B(B),
    .OPERATION(OPERATION),
    .RESULT(RESULT),
    .ZERO(ZERO)
);

task add(bit[SIZE-1:0] a, bit[SIZE-1:0] b);
    set_input(0,a,b);
endtask

task sub_task(bit[SIZE-1:0] a, bit[SIZE-1:0] b);
    set_input(1,a,b);
endtask

task less_than(bit[SIZE-1:0] a, bit[SIZE-1:0] b);
   set_input(2,a,b);
endtask

task greater_or_equal_than(bit[SIZE-1:0] a, bit[SIZE-1:0] b);
   set_input(3,a,b);
endtask

task and_task(bit[SIZE-1:0] a, bit[SIZE-1:0] b);
   set_input(4,a,b);
endtask

task or_task(bit[SIZE-1:0] a, bit[SIZE-1:0] b);
   set_input(5,a,b);
endtask

task xnor_task(bit[SIZE-1:0] a, bit[SIZE-1:0] b);
   set_input(6,a,b);
endtask

task left_shift(bit[SIZE-1:0] a, bit[SIZE-1:0] b);
   set_input(7,a,b);
endtask

task right_shift(bit[SIZE-1:0] a, bit[SIZE-1:0] b);
   set_input(8,a,b);
endtask

task set_input(bit[3:0] op, bit[SIZE-1:0] a, bit[SIZE-1:0] b);
    OPERATION = op;
    A = a;
    B = b;
endtask

task sleep();
    #(SLEEP_TIME);
endtask

endmodule