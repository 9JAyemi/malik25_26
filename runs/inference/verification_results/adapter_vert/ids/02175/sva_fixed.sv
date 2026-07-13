module Comparator_sva (
    input logic in1,
    input logic in2,
    input logic out,
    input logic b00,
    input logic b01,
    input logic b10,
    input logic clk_in_1
);

property GreaterThaneotid; @(posedge clk_in_1) (in1) > (in2) |-> (out) == 2'b01 ; endproperty
assert property (GreaterThaneotid);

property EqualCheckeotid; @(posedge clk_in_1) (in1) == (in2) |-> (out) == 2'b00 ; endproperty
assert property (EqualCheckeotid);

property LessThaneotid; @(posedge clk_in_1) (in1) < (in2) |-> (out) == 2'b10 ; endproperty
assert property (LessThaneotid);

endmodule