module nor4b_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D_N,
    input logic Y,
    input logic inputs,
    input logic b0,
    input logic b0000,
    input logic b1,
    input logic clk_in_17
);

property SyncCheckeotid; @(posedge clk_in_17) (A) |-> (inputs) ;endproperty
assert property (SyncCheckeotid);

property SyncCheckeotid_2; @(posedge clk_in_17) (B) |-> (inputs) ;endproperty
assert property (SyncCheckeotid_2);

property SyncCheckeotid_3; @(posedge clk_in_17) (C) |-> (inputs) ;endproperty
assert property (SyncCheckeotid_3);

property SyncCheckeotid_4; @(posedge clk_in_17) (D_N) |-> (inputs) ;endproperty
assert property (SyncCheckeotid_4);

property SyncSafeeotid; @(posedge clk_in_17) (inputs) != 4'b0000 |->  (Y) == 1'b1 ;endproperty
assert property (SyncSafeeotid);

property SyncSafeeotid_2; @(posedge clk_in_17) (inputs) != 4'b0000 |->  (Y) != 1'b0 ;endproperty
assert property (SyncSafeeotid_2);

endmodule