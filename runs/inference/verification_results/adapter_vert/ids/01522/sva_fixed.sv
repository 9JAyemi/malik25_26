module four_bit_counter_sva (
    input logic clk,
    input logic count,
    input logic reset,
    input logic b1,
    input logic reg_15
);

property ResetSynceotid; @(posedge clk) (reset) |-> count == 0 ;endproperty
assert property (ResetSynceotid);

property SyncCounteotid; @(posedge clk) (reset) != 1'b1  |->  count == reg_15 ;endproperty
assert property (SyncCounteotid);

endmodule