module binary_counter_sva (
    input logic clk,
    input logic q,
    input logic reset,
    input logic b0000,
    input logic b1,
    input logic b1111
);

property ResetSynceotid; @(posedge clk) (reset) |-> (q) == 4'b0000 ;endproperty
assert property (ResetSynceotid);

property ResetSynceotid_2; @(posedge clk) (reset) &&  (q) == 4'b1111  |-> (q) == 4'b0000; endproperty
assert property (ResetSynceotid_2);

property SyncInceotid; @(posedge clk) (reset) != 1'b1  &&  (q) != 4'b1111  |-> (q) == (q + 1'b1); endproperty
assert property (SyncInceotid);

endmodule