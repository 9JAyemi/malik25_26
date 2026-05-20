module mux2to1_sva (
    input logic A1_N,
    input logic A2_N,
    input logic B1,
    input logic B2,
    input logic Y,
    input logic b1,
    input logic clk_in_13
);

property SyncEqeotid; @(posedge clk_in_13) (A1_N) && (A2_N) &&  (B2) |->  (Y) == 1'b1 ;endproperty
assert property (SyncEqeotid);

property SyncEqeotid_2; @(posedge clk_in_13) (A1_N) &&  (!A2_N) &&  (B1) |->  (Y) == 1'b1 ;endproperty
assert property (SyncEqeotid_2);

property SyncEqeotid_3; @(posedge clk_in_13)  (!A1_N) && (A2_N) &&  (B2) |->  (Y) == 1'b1 ;endproperty
assert property (SyncEqeotid_3);

property SyncEqeotid_4; @(posedge clk_in_13)  (!A1_N) &&  (!A2_N) &&  (B1) |->  (Y) == 1'b1 ;endproperty
assert property (SyncEqeotid_4);

endmodule