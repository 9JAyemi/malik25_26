module flip_flop_sva (
    input logic CLK,
    input logic D,
    input logic DE,
    input logic Q,
    input logic SCD,
    input logic SCE,
    input logic b1
);

property ClockSynceotid; @(posedge CLK) (DE) |-> Q == D ; endproperty
assert property (ClockSynceotid);

property SyncLoadeotid; @(posedge CLK) (DE) != 1'b1 && (SCE) |-> Q == SCD ; endproperty
assert property (SyncLoadeotid);

endmodule