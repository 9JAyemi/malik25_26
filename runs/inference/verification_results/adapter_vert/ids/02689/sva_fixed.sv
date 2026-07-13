module bitwise_operators_sva (
    input logic A,
    input logic B,
    input logic and_res,
    input logic not_res,
    input logic or_res,
    input logic xor_res,
    input logic clk_in_1
);

property BitwiseAndeotid; @(posedge clk_in_1) ( A ) & ( B ) |-> ( and_res ) ; endproperty
assert property (BitwiseAndeotid);

property BitwiseOrEeotid; @(posedge clk_in_1) ( A ) | ( B ) |-> ( or_res ) ; endproperty
assert property (BitwiseOrEeotid);

property BitwiseXOReotid; @(posedge clk_in_1) ( A ) ^ ( B ) |-> ( xor_res ) ; endproperty
assert property (BitwiseXOReotid);

property NotAeotid; @(posedge clk_in_1)  ( A )  !=  ( B )  |-> ( not_res ) ; endproperty
assert property (NotAeotid);

endmodule