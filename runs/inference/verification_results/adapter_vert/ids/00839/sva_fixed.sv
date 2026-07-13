module binary_to_gray_sva (
    input logic binary,
    input logic gray,
    input logic clk_in_12
);

property BinaryToGrayeotid; @(posedge clk_in_12) (binary) |-> (gray) == (binary); endproperty
assert property (BinaryToGrayeotid);

property GraySynceotid; @(posedge clk_in_12) (binary) |-> (gray) == (binary); endproperty
assert property (GraySynceotid);

property GraySynceotid_2; @(posedge clk_in_12) (binary) |-> (gray) == (binary); endproperty
assert property (GraySynceotid_2);

property GraySynceotid_3; @(posedge clk_in_12) (binary) |-> (gray) == (binary); endproperty
assert property (GraySynceotid_3);

endmodule