module and4bb_sva (
    input logic A_N,
    input logic B_N,
    input logic C,
    input logic D,
    input logic X,
    input logic clk_in_15
);

property SyncIneotid; @(posedge clk_in_15) (A_N) |-> (X) ;endproperty
assert property (SyncIneotid);

property SyncIneotid_2; @(posedge clk_in_15) (B_N) |-> (X) ;endproperty
assert property (SyncIneotid_2);

property SyncIneotid_3; @(posedge clk_in_15) (C) |-> (X) ;endproperty
assert property (SyncIneotid_3);

property SyncIneotid_4; @(posedge clk_in_15) (D) |-> (X) ;endproperty
assert property (SyncIneotid_4);

endmodule