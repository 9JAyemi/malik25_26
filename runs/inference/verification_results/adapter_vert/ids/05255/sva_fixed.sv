module binary_multiplier_sva (
    input logic a,
    input logic b,
    input logic clk,
    input logic reset,
    input logic result
);

property ResetSynceotid; @(posedge clk) (reset) |-> result == 0 ;endproperty
assert property (ResetSynceotid);

property ValidOnReseteotid; @(posedge clk) ( !reset ) |-> result == ( a * b ) ;endproperty
assert property (ValidOnReseteotid);

endmodule