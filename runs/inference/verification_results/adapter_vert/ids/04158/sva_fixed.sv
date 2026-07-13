module binary_add_sub_sva (
    input logic A,
    input logic B,
    input logic Y,
    input logic mode,
    input logic clk_in_1
);

property AddSynceotid; @(posedge clk_in_1) (mode) == (0) |-> (Y) == (A + B) ; endproperty
assert property (AddSynceotid);

property SubSynceotid; @(posedge clk_in_1) (mode) != 0  |-> (Y) == (A +  ( ~B ) + 1) ; endproperty
assert property (SubSynceotid);

endmodule