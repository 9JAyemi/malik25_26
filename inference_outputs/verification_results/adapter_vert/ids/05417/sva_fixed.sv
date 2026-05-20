module counter_4bit_sync_reset_load_sva (
    input logic clk,
    input logic count,
    input logic data_in,
    input logic load,
    input logic reset,
    input logic b0
);

property ResetSynceotid; @(posedge clk) (reset) |-> count == 4'b0 ;endproperty
assert property (ResetSynceotid);

property LoadSynceotid; @(posedge clk) (load) && !(reset)  |-> count == data_in ;endproperty
assert property (LoadSynceotid);

property SyncCounteotid; @(posedge clk) !(reset) && ! (load)  |-> count == count + 1 ;endproperty
assert property (SyncCounteotid);

endmodule