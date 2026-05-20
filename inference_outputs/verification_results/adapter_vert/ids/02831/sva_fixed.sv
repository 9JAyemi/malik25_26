module flip_flop_sva (
    input logic clk,
    input logic data,
    input logic q,
    input logic q_bar,
    input logic rst,
    input logic b0,
    input logic b1
);

property ResetSynceotid; @(posedge clk) (rst) |-> (q == 1'b1) && (q_bar == 1'b0) ; endproperty
assert property (ResetSynceotid);

property ResetSynceotid_2; @(posedge clk) (rst) |-> (q != data) && (q_bar != data) ; endproperty
assert property (ResetSynceotid_2);

property ResetSynceotid_3; @(posedge clk) (rst) &&  (  data  != 0  &&  data  != 1  ) |-> (q != data) && (q_bar != data) ; endproperty
assert property (ResetSynceotid_3);

property ResetSynceotid_4; @(posedge clk) (rst) &&  (  data  == 0  ||  data  == 1  ) |-> (q == 1'b1) && (q_bar == 1'b0) ; endproperty
assert property (ResetSynceotid_4);

endmodule