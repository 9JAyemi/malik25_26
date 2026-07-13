module binary_counter_sva (
    input logic clk,
    input logic count,
    input logic reset,
    input logic b1
);

property ResetSynceotid; @(posedge clk) (reset) |-> count == 0 ;endproperty
assert property (ResetSynceotid);

property SyncCounteotid; @(posedge clk) (reset) != 1'b1  |->  count == count + 1 ;endproperty
assert property (SyncCounteotid);

endmodule