module RegisterAdd__parameterized5_sva (
    input logic AR,
    input logic CLK,
    input logic E,
    input logic Q_reg,
    input logic b0000000,
    input logic data_14
);

property ResetSynceotid; @(posedge CLK) ( !AR ) |-> Q_reg == 7'b0000000 ; endproperty
assert property (ResetSynceotid);

property SyncLoadeotid; @(posedge CLK) (  AR ) && (  E ) |-> Q_reg == data_14 ; endproperty
assert property (SyncLoadeotid);

endmodule