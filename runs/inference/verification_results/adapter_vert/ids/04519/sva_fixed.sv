module nor_and_sva (
    input logic A,
    input logic C,
    input logic Y,
    input logic nor1_out,
    input logic clk_reset_13,
    input logic nor2_out
);

property ResetSynceotid; @(negedge clk_reset_13) (A) |-> (nor1_out) ; endproperty
assert property (ResetSynceotid);

property ResetSynceotid_2; @(negedge clk_reset_13) (C) |-> (nor2_out) ; endproperty
assert property (ResetSynceotid_2);

property ResetSynceotid_3; @(negedge clk_reset_13) (A) && @(negedge clk_reset_13) (C) |-> (Y) ; endproperty
assert property (ResetSynceotid_3);

endmodule