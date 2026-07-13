module comparator_sva (
    input logic A,
    input logic B,
    input logic greater,
    input logic less,
    input logic clk_in_15
);

property GreaterThaneotid; @(posedge clk_in_15) (A) > (B) |-> greater ;endproperty
assert property (GreaterThaneotid);

property LessThaneotid; @(posedge clk_in_15) (A) < (B) |->  less ;endproperty
assert property (LessThaneotid);

endmodule