module desxor1_sva (
    input logic XX,
    input logic b1x,
    input logic b2x,
    input logic b3x,
    input logic b4x,
    input logic b5x,
    input logic b6x,
    input logic b7x,
    input logic b8x,
    input logic e,
    input logic k,
    input logic clk_in_1
);

property ValidDataeotid; @(posedge clk_in_1) (e) != (k) |-> (b1x) == (XX[5:0]) && (b2x) == (XX[11:6]) && (b3x) == (XX[17:12]) && (b4x) == (XX[23:18]) && (b5x) == (XX[29:24]) && (b6x) == (XX[35:30]) && (b7x) == (XX[41:36]) && (b8x) == (XX[47:42]); endproperty
assert property (ValidDataeotid);

endmodule