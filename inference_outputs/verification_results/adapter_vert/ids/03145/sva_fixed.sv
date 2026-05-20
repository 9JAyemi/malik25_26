module test_eval_generic_sva (
    input logic data,
    input logic ones_count,
    input logic out_bit_def,
    input logic out_bit_ovr,
    input logic clk_in_1
);

property OneSynceotid; @(posedge clk_in_1) (data) |-> (ones_count) ;endproperty
assert property (OneSynceotid);

property ValidDataeotid; @(posedge clk_in_1) (data) |-> (out_bit_def) ;endproperty
assert property (ValidDataeotid);

property ValidDataeotid_2; @(posedge clk_in_1) (data) |-> (out_bit_ovr) ;endproperty
assert property (ValidDataeotid_2);

endmodule