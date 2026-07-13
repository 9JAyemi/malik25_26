module binary_counter_sva (
    input logic clk,
    input logic count,
    input logic rst,
    input logic b1,
    input logic reg_18
);

property ResetSynceotid; @(posedge clk) (rst) |-> count == 0 ;endproperty
assert property (ResetSynceotid);

property SyncCounteotid; @(posedge clk) (rst) != 1'b1  |->  count == reg_18 ;endproperty
assert property (SyncCounteotid);

endmodule