module multiplier_sva (
    input logic a,
    input logic b,
    input logic clk,
    input logic product,
    input logic reset,
    input logic sel,
    input logic sum
);

property ResetSynceotid; @(posedge clk) (reset) |-> (product == 0) && (sum == 0) ;endproperty
assert property (ResetSynceotid);

property ValidDataeotid; @(posedge clk) ( !reset ) &&  (  sel ) |-> (sum == a + b) ;endproperty
assert property (ValidDataeotid);

property ValidDataeotid_2; @(posedge clk) ( !reset ) &&  ( !sel ) |-> (product == a * b) ;endproperty
assert property (ValidDataeotid_2);

endmodule