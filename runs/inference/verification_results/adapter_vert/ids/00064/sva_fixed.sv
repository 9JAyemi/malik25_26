module and_gate_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic VPWR,
    input logic X,
    input logic clk_signal_14
);

property SyncReqeotid; @(posedge clk_signal_14) (A1) && (A2) && (B1) && (VPWR) |-> (X); endproperty
assert property (SyncReqeotid);

property SyncReqeotid_2; @(posedge clk_signal_14) (A1) && (A2) && (B1) && (VPWR) |-> (X); endproperty
assert property (SyncReqeotid_2);

property SyncReqeotid_3; @(posedge clk_signal_14) (A1) && (A2) && (B1) && (VPWR) |-> (X); endproperty
assert property (SyncReqeotid_3);

endmodule