module binary_subtractor_32bit_sva (
    input logic A,
    input logic B,
    input logic B_comp,
    input logic S,
    input logic clk_in_12
);

property SubSynceotid; @(posedge clk_in_12) (B) |-> (B_comp) ;endproperty
assert property (SubSynceotid);

property SyncSubeotid; @(posedge clk_in_12) (A) != (B) |-> (S) == (A + B_comp) ;endproperty
assert property (SyncSubeotid);

property SyncSubeotid_2; @(posedge clk_in_12) (B) |-> (S) == (A + B_comp) ;endproperty
assert property (SyncSubeotid_2);

endmodule