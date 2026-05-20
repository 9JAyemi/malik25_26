module binary_counter_sva (
    input logic clk,
    input logic count,
    input logic reset,
    input logic b0000,
    input logic b0001,
    input logic b1,
    input logic b1111
);

property ResetSynceotid; @(posedge clk) (reset) |-> count == 4'b0000 ;endproperty
assert property (ResetSynceotid);

property SyncCounteotid; @(posedge clk) (reset) != 1'b1 &&  (count) != 4'b1111  |->  (count) == (count + 4'b0001) ;endproperty
assert property (SyncCounteotid);

property ResetSynceotid_2; @(posedge clk) (reset) != 1'b1 &&  (count) == 4'b1111  |->  (count) == 4'b0000 ;endproperty
assert property (ResetSynceotid_2);

endmodule