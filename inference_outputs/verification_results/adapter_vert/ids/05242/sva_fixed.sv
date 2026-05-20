module bitwise_operators_sva (
    input logic a,
    input logic and_out,
    input logic b,
    input logic not_out,
    input logic or_out,
    input logic xor_out,
    input logic b1,
    input logic clk_in_1
);

property BitwiseAndeotid; @(posedge clk_in_1) (a) && (b) |-> and_out == (a) && (b) ; endproperty
assert property (BitwiseAndeotid);

property BitwiseOrEeotid; @(posedge clk_in_1) (a) || (b) |-> or_out == (a) || (b) ; endproperty
assert property (BitwiseOrEeotid);

property BitwiseXOReotid; @(posedge clk_in_1) (a) != (b) |-> xor_out == (a) != (b) ; endproperty
assert property (BitwiseXOReotid);

property BitwiseNotEqeotid; @(posedge clk_in_1)  (a)  !=  (not_out)  |-> 1'b1 ; endproperty
assert property (BitwiseNotEqeotid);

endmodule