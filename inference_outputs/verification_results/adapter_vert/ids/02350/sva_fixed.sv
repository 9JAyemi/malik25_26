module top_module_sva (
    input logic or_out,
    input logic out,
    input logic reset,
    input logic xor_out,
    input logic clk_reset_17
);

property ResetSynceotid; @(negedge clk_reset_17) (reset) |-> (or_out) ;endproperty
assert property (ResetSynceotid);

property ResetSynceotid_2; @(negedge clk_reset_17) (reset) |-> (xor_out) ;endproperty
assert property (ResetSynceotid_2);

property ResetSynceotid_3; @(negedge clk_reset_17) (reset) |-> (out) ;endproperty
assert property (ResetSynceotid_3);

endmodule