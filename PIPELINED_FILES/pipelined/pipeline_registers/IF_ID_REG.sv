`ifndef IF_ID_REG_GUARD
`define IF_ID_REG_GUARD
module IF_ID_REG #(parameter DATA_SIZE = 32, parameter ADDR_SIZE = 10) (
    input clk,
    input clear,
    input [ADDR_SIZE-1:0] pc_if,
    input [DATA_SIZE-1:0] inst_if,
    output reg [ADDR_SIZE-1:0] pc_id,
    output reg [DATA_SIZE-1:0] inst_id
);

always_ff @(posedge clk or posedge clear) begin
    if(clear == 1) begin
        pc_id <= 0;
        inst_id <= 0;
    end else begin
        pc_id <= pc_if;
        inst_id <= inst_if;
    end 
end

endmodule

`endif 