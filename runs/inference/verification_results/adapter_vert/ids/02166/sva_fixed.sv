module accumulator_sva (
    input logic clk,
    input logic data_in,
    input logic out,
    input logic rst,
    input logic sum,
    input logic b0,
    input logic b1
);

property ResetSynceotid; @(posedge clk) (rst) |-> sum == 8'b0 ;endproperty
assert property (ResetSynceotid);

property SyncAccumulateeotid; @(posedge clk) (rst) != 1'b1  |-> sum == data_in + sum; endproperty
assert property (SyncAccumulateeotid);

property SyncAccumulateeotid_2; @(posedge clk) (rst) != 1'b1  |-> out == sum; endproperty
assert property (SyncAccumulateeotid_2);

endmodule