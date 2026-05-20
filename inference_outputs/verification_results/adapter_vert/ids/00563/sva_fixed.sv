module comparator_block_sva (
    input logic a,
    input logic a_gt_b,
    input logic b,
    input logic a_eq_b,
    input logic a_lt_b,
    input logic clk_in_17
);

property ClockSynceotid; @(posedge clk_in_17) (a) |-> (a_gt_b) ; endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge clk_in_17) (b) |-> (a_lt_b) ; endproperty
assert property (ClockSynceotid_2);

property SyncEqeotid; @(posedge clk_in_17) (a) == (b) |-> (a_eq_b) ; endproperty
assert property (SyncEqeotid);

endmodule