module bitwise_or_twos_complement_sva (
    input logic a,
    input logic diff,
    input logic or_result,
    input logic out,
    input logic twos_comp_result,
    input logic clk_in_1
);

property BitwiseOReotid; @(posedge clk_in_1) (a) |-> (or_result) ;endproperty
assert property (BitwiseOReotid);

property TwoComplementeotid; @(posedge clk_in_1) (a) |-> (twos_comp_result) ;endproperty
assert property (TwoComplementeotid);

property DiffCheckeotid; @(posedge clk_in_1) (a) |-> (diff) ;endproperty
assert property (DiffCheckeotid);

property SyncOuteotid; @(posedge clk_in_1) (or_result) |-> (out) ;endproperty
assert property (SyncOuteotid);

endmodule