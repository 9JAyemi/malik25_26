module up_counter_sva (
    input logic clk,
    input logic count,
    input logic out,
    input logic reset,
    input logic b0,
    input logic b1,
    input logic reg_15,
    input logic reg_16
);

property ResetSynceotid; @(posedge clk) (reset) |-> (count == 4'b0) && (out == 1'b0) ;endproperty
assert property (ResetSynceotid);

property SyncIncrseotid; @(posedge clk) (reset) != 1'b1  |->  (count == reg_15) && (out != reg_16) ;endproperty
assert property (SyncIncrseotid);

endmodule