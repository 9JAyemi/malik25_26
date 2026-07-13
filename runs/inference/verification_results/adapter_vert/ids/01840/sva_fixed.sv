module binary_counter_sva (
    input logic clk,
    input logic count,
    input logic data,
    input logic load,
    input logic rst,
    input logic b0,
    input logic b1
);

property ResetSynceotid; @(posedge clk) (rst) |-> count == 4'b0 ;endproperty
assert property (ResetSynceotid);

property LoadSynceotid; @(posedge clk) (rst) &&  (load) |-> count == data ;endproperty
assert property (LoadSynceotid);

property SyncCounteotid; @(posedge clk) (rst) &&  (!load)  |-> count == count + 4'b1 ;endproperty
assert property (SyncCounteotid);

endmodule