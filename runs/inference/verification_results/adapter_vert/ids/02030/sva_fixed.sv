module mult_16x16_sva (
    input logic A,
    input logic B,
    input logic Z,
    input logic clk_10,
    input logic clk_18,
    input logic clk_19,
    input logic clk_in_15
);

property MultiplySynceotid; @(posedge clk_in_15) (A) * (B) == (Z); endproperty
assert property (MultiplySynceotid);

property MultiplySynceotid_2; @(posedge clk_19) (A) * (B) == (Z); endproperty
assert property (MultiplySynceotid_2);

property Multiplyeotid; @(posedge clk_18) (A) * (B) == (Z); endproperty
assert property (Multiplyeotid);

property Multiplyeotid_2; @(posedge clk_10) (A) * (B) == (Z); endproperty
assert property (Multiplyeotid_2);

endmodule