module sync_signal_sva (
    input logic clk,
    input logic falling,
    input logic in,
    input logic out,
    input logic rising,
    input logic shiftreg,
    input logic b0110
);

property SyncIneotid; @(posedge clk) (in) |-> (shiftreg) == (4'b0110) ;endproperty
assert property (SyncIneotid);

property SyncRiseeotid; @(posedge clk) (in) |-> (rising) ;endproperty
assert property (SyncRiseeotid);

property SyncFalleotid; @(posedge clk) (in) |-> (falling) ;endproperty
assert property (SyncFalleotid);

property SyncCheckeotid; @(posedge clk) (in) |-> (out) == (shiftreg) ;endproperty
assert property (SyncCheckeotid);

endmodule