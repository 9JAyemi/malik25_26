module subtractor_sva (
    input logic A,
    input logic B,
    input logic Y,
    input logic b0000,
    input logic bx000,
    input logic clk_in_1
);

property SubSynceotid; @(posedge clk_in_1) (A) - (B) == (Y) ;endproperty
assert property (SubSynceotid);

property SyncSubeotid; @(posedge clk_in_1) (A) != (B) |-> (Y) != 4'bx000 ;endproperty
assert property (SyncSubeotid);

property SyncCheckeotid; @(posedge clk_in_1) (A) != (B) &&  (  (A) - (B)  != 0 ) |-> (Y) != 4'b0000 ;endproperty
assert property (SyncCheckeotid);

endmodule