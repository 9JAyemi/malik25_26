module mag_comparator_sva (
    input logic A,
    input logic B,
    input logic EQ,
    input logic GT,
    input logic LT,
    input logic b1,
    input logic clk_in_15
);

property EqualOnClockeotid; @(posedge clk_in_15) (A) == (B) |-> (EQ) == 1'b1 ; endproperty
assert property (EqualOnClockeotid);

property GreaterThaneotid; @(posedge clk_in_15) (A) > (B) |-> (GT) == 1'b1 ; endproperty
assert property (GreaterThaneotid);

property LessThaneotid; @(posedge clk_in_15) (A) < (B) |-> (LT) == 1'b1 ; endproperty
assert property (LessThaneotid);

endmodule