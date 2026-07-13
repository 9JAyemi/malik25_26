module bitwise_or_logical_or_not_sva (
    input logic a,
    input logic b,
    input logic not_a,
    input logic not_b,
    input logic or_bitwise,
    input logic or_logical,
    input logic out_not,
    input logic clk_in_1
);

property BitwiseORorLogicalOR; @(posedge clk_in_1) (a) |-> (or_bitwise) ; endproperty
assert property (BitwiseORorLogicalOR);

property ORorORorOR; @(posedge clk_in_1) (a) && (b) |-> (or_logical) ; endproperty
assert property (ORorORorOR);

property NotAorNotB; @(posedge clk_in_1) (a) |-> (not_a) ; endproperty
assert property (NotAorNotB);

property NotAorNotBorNotBoth; @(posedge clk_in_1) (b) |-> (not_b) ; endproperty
assert property (NotAorNotBorNotBoth);

property NotAandNotB; @(posedge clk_in_1) (a) && (b) |-> (out_not) ; endproperty
assert property (NotAandNotB);

endmodule