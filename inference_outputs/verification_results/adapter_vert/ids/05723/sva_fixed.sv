module mux_add_sub_sva (
    input logic Q,
    input logic a,
    input logic add_sub_ctrl,
    input logic add_sub_out,
    input logic b,
    input logic mux_enable,
    input logic b1,
    input logic clk_in_12,
    input logic h0
);

property AddSynceotid; @(posedge clk_in_12) (add_sub_ctrl) |-> (add_sub_out) == (a + b) ; endproperty
assert property (AddSynceotid);

property SyncCheckeotid; @(posedge clk_in_12) (add_sub_ctrl) != 1'b1  |-> (add_sub_out) == (a - b) ; endproperty
assert property (SyncCheckeotid);

property ValidDataeotid; @(posedge clk_in_12) (mux_enable) |-> (Q) == (add_sub_out[3:0]) ; endproperty
assert property (ValidDataeotid);

property SyncCheckeotid_2; @(posedge clk_in_12) (mux_enable) != 1'b1  |-> (Q) == 4'h0 ; endproperty
assert property (SyncCheckeotid_2);

property EnableSynceotid; @(posedge clk_in_12) (add_sub_ctrl) == (mux_enable) ; endproperty
assert property (EnableSynceotid);

endmodule