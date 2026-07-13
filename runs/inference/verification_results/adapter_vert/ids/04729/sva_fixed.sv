module binary_to_gray_sva (
    input logic binary_in,
    input logic clk,
    input logic gray_out
);

property ClockSynceotid; @(posedge clk) ( binary_in ) |-> ( gray_out ) ;endproperty
assert property (ClockSynceotid);

property BinaryToGrayeotid; @(posedge clk) ( binary_in ) |-> ( gray_out ) ;endproperty
assert property (BinaryToGrayeotid);

property GraySynceotid; @(posedge clk) ( binary_in ) |-> ( gray_out ) ;endproperty
assert property (GraySynceotid);

property GraySynceotid_2; @(posedge clk) ( binary_in ) |-> ( gray_out ) ;endproperty
assert property (GraySynceotid_2);

endmodule