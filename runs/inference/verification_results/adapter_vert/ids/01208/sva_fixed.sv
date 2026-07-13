module control_sva (
    input logic clk,
    input logic control_o,
    input logic en,
    input logic en_mem,
    input logic imm,
    input logic pc_op,
    input logic rst,
    input logic should_branch,
    input logic b00,
    input logic b1,
    input logic b10
);

property ResetSynceotid; @(posedge clk) (rst) |-> control_o == 0 && pc_op == 0 ;endproperty
assert property (ResetSynceotid);

property EnableSynceotid; @(posedge clk) (rst) != 1'b1 &&  (en)  |-> control_o[0] == en_mem && control_o[1] == should_branch && control_o[2] == imm ;endproperty
assert property (EnableSynceotid);

property ValidOpeotid; @(posedge clk) (rst) != 1'b1 &&  (en)  &&  (imm)  |-> pc_op == 2'b10 ;endproperty
assert property (ValidOpeotid);

property ValidPcOpeotid; @(posedge clk) (rst) != 1'b1 &&  (en)  &&  ( ! (imm)  ) |-> pc_op == 2'b00 ;endproperty
assert property (ValidPcOpeotid);

endmodule