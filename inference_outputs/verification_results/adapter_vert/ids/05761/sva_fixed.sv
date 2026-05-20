module my_2to1_mux_sva (
    input logic A,
    input logic B,
    input logic MO,
    input logic S,
    input logic clk_in_15
);

property SyncEqeotid; @(posedge clk_in_15) (S) |-> (MO) == (B) ; endproperty
assert property (SyncEqeotid);

property SyncEqeotid_2; @(posedge clk_in_15) (S) != 1 |-> (MO) == (A) ; endproperty
assert property (SyncEqeotid_2);

endmodule