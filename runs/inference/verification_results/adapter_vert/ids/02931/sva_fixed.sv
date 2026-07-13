module comparator_sva (
    input logic a,
    input logic b,
    input logic eq,
    input logic gt,
    input logic lt,
    input logic b0,
    input logic b1,
    input logic clk_in_13
);

property GreaterThaneotid; @(posedge clk_in_13) (a) > (b) |-> (gt) == 1'b1 && (lt) == 1'b0 && (eq) == 1'b0 ;endproperty
assert property (GreaterThaneotid);

property LessThaneotid; @(posedge clk_in_13) (a) < (b) |-> (gt) == 1'b0 && (lt) == 1'b1 && (eq) == 1'b0 ;endproperty
assert property (LessThaneotid);

property EqualToeotid; @(posedge clk_in_13) (a) == (b) |-> (gt) == 1'b0 && (lt) == 1'b0 && (eq) == 1'b1 ;endproperty
assert property (EqualToeotid);

endmodule