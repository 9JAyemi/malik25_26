module xnor2_sva (
    input logic A,
    input logic B,
    input logic Y,
    input logic clk_in_1
);

property SyncEqeotid; @(posedge clk_in_1) (Y) == ( ~(A ^ B) ); endproperty
assert property (SyncEqeotid);

property SyncEqeotid_2; @(posedge clk_in_1) (Y) == ( ~(A ^ B) ); endproperty
assert property (SyncEqeotid_2);

endmodule