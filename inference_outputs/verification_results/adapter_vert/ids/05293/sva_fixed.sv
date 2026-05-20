module sync_counter_sva (
    input logic clk,
    input logic count,
    input logic data,
    input logic load,
    input logic rst
);

property ResetSynceotid; @(posedge clk) (rst) |-> count == 0 ;endproperty
assert property (ResetSynceotid);

property LoadSynceotid; @(posedge clk) (load) |-> count == data ;endproperty
assert property (LoadSynceotid);

property SyncCounteotid; @(posedge clk) ( !rst && !load ) |-> count == count + 1 ;endproperty
assert property (SyncCounteotid);

endmodule