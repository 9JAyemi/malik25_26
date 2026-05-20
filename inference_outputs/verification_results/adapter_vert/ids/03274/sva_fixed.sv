module dffr_sva (
    input logic C,
    input logic D,
    input logic Q,
    input logic R,
    input logic b0
);

property ClockResetSynceotid; @(posedge C) (R) |-> Q == D ; endproperty
assert property (ClockResetSynceotid);

property ResetSynceotid; @(posedge C) (R) |-> Q == 1'b0 ; endproperty
assert property (ResetSynceotid);

endmodule