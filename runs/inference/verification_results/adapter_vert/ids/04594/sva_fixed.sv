module comparator_4bit_sva (
    input logic A,
    input logic B,
    input logic result,
    input logic b00,
    input logic b01,
    input logic b10,
    input logic clk_in_15
);

property GreaterThaneotid; @(posedge clk_in_15) (A) > (B) |-> result == 2'b01 ; endproperty
assert property (GreaterThaneotid);

property LessThaneotid; @(posedge clk_in_15) (A) < (B) |-> result == 2'b10 ; endproperty
assert property (LessThaneotid);

property EqualToeotid; @(posedge clk_in_15) (A) == (B) |-> result == 2'b00 ; endproperty
assert property (EqualToeotid);

endmodule