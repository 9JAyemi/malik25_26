module mux_2_1_sva (
    input logic a,
    input logic b,
    input logic out,
    input logic sel,
    input logic b0,
    input logic clk_in_1
);

property ClockSynceotid; @(posedge clk_in_1) (sel) == (1'b0) |-> (out) == (a) ; endproperty
assert property (ClockSynceotid);

property SyncEqeotid; @(posedge clk_in_1) (sel) != 1'b0  |-> (out) == (b) ; endproperty
assert property (SyncEqeotid);

endmodule