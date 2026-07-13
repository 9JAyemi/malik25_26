module top_module_sva (
    input logic clk,
    input logic difference_output,
    input logic product_output,
    input logic reset,
    input logic sum_output
);

property ResetSynceotid; @(posedge clk) (reset) |-> (sum_output) == 0 ;endproperty
assert property (ResetSynceotid);

property ResetSynceotid_2; @(posedge clk) (reset) |-> (product_output) == 0 ;endproperty
assert property (ResetSynceotid_2);

property ResetSynceotid_3; @(posedge clk) (reset) |-> (difference_output) == 0 ;endproperty
assert property (ResetSynceotid_3);

endmodule