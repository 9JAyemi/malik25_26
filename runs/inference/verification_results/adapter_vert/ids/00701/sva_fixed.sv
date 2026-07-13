module bin2gray_sva (
    input logic binary,
    input logic gray,
    input logic clk_in_17
);

property BinaryToGrayeotid; @(posedge clk_in_17) (binary) |-> (gray) == (binary); endproperty
assert property (BinaryToGrayeotid);

property GraySynceotid; @(posedge clk_in_17) (binary) |-> (gray) == ( { binary[3], binary[2] ^ binary[3], binary[1] ^ binary[2], binary[0] ^ binary[1] } ); endproperty
assert property (GraySynceotid);

property GraySynceotid_2; @(posedge clk_in_17) (binary) |-> (gray) == ( { binary[3], binary[2] ^ binary[3], binary[1] ^ binary[2], binary[0] ^ binary[1] } ); endproperty
assert property (GraySynceotid_2);

endmodule