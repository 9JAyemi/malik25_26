module binary_counter_sva (
    input logic CLK,
    input logic CLR_B,
    input logic DATA_IN,
    input logic LOAD,
    input logic Q,
    input logic MAX_VALUE,
    input logic b1,
    input logic reg_14
);

property ResetSynceotid; @(posedge CLK) (CLR_B) |-> Q == 0 ;endproperty
assert property (ResetSynceotid);

property LoadSynceotid; @(posedge CLK) (LOAD) |-> Q == DATA_IN ;endproperty
assert property (LoadSynceotid);

property ClockSynceotid; @(posedge CLK) (Q == MAX_VALUE - 1) |-> Q == 0 ;endproperty
assert property (ClockSynceotid);

property SyncCounteotid; @(posedge CLK) (CLR_B) != 1'b1 && (LOAD) != 1'b1 &&  (Q != MAX_VALUE - 1)  |-> Q == reg_14 ;endproperty
assert property (SyncCounteotid);

endmodule