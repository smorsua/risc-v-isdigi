`ifndef IF_ID_REG_GUARD
`define IF_ID_REG_GUARD
module IF_ID_REG #(parameter DATA_SIZE = 32, parameter ADDR_SIZE = 10) (
    input clk,
    input enable,
    input [ADDR_SIZE-1+2:0] pc_if,
    input [DATA_SIZE-1:0] inst_if,
    output reg [ADDR_SIZE-1+2:0] pc_id,
    output [DATA_SIZE-1:0] inst_id
);

always_ff @(posedge clk) begin
    if(enable == 1) begin
        pc_id <= pc_if;
    end else begin
        pc_id <= pc_id;
    end
end

assign inst_id = inst_if;

endmodule

`endif