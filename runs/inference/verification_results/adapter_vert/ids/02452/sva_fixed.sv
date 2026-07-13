module top_module_sva (
    input logic in,
    input logic out,
    input logic clk_in_1
);

property ValidDataeotid; @(posedge clk_in_1) (in) |-> (out) ;endproperty
assert property (ValidDataeotid);

property ValidDataeotid_2; @(posedge clk_in_1) (in) |-> (out) ;endproperty
assert property (ValidDataeotid_2);

property ValidDataeotid_3; @(posedge clk_in_1) (in) |-> (out) ;endproperty
assert property (ValidDataeotid_3);

property ValidDataeotid_4; @(posedge clk_in_1) (in) |-> (out) ;endproperty
assert property (ValidDataeotid_4);

endmodule