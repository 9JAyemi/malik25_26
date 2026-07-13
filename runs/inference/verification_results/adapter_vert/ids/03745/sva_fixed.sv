module counter_4bit_sync_reset_sva (
    input logic CK,
    input logic Q,
    input logic RST,
    input logic b0,
    input logic b1
);

property ResetSynceotid; @(posedge CK) (RST) |-> (Q) == 4'b0 ;endproperty
assert property (ResetSynceotid);

property SyncIncrseotid; @(posedge CK) (RST) != 1'b1  |-> (Q) == (Q + 1) ;endproperty
assert property (SyncIncrseotid);

endmodule