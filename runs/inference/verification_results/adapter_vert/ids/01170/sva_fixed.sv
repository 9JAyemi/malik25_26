module binary_counter_sva (
    input logic clk,
    input logic count,
    input logic rst,
    input logic b0000,
    input logic b1,
    input logic reg_14
);

property ResetSynceotid; @(posedge clk) (rst) |-> count == 4'b0000 ;endproperty
assert property (ResetSynceotid);

property SyncUpeotid; @(posedge clk) (rst) != 1'b1  |->  count == reg_14 ;endproperty
assert property (SyncUpeotid);

endmodule