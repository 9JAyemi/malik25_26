module binary_to_gray_sva (
    input logic in,
    input logic out,
    input logic clk_in_1
);

property ClockSynceotid; @(posedge clk_in_1) (in) |-> (out) ;endproperty
assert property (ClockSynceotid);

property BinaryToGrayeotid; @(posedge clk_in_1) (in) |-> (out) ;endproperty
assert property (BinaryToGrayeotid);

property GraySynceotid; @(posedge clk_in_1) (in) |-> (out) ;endproperty
assert property (GraySynceotid);

property GraySynceotid_2; @(posedge clk_in_1) (in) |-> (out) ;endproperty
assert property (GraySynceotid_2);

endmodule