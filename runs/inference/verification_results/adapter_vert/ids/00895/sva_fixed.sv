module binary_counter_sva (
    input logic clk,
    input logic count,
    input logic rst,
    input logic b0,
    input logic reg_14
);

property ResetSynceotid; @(posedge clk) (rst) |-> count == 3'b0 ;endproperty
assert property (ResetSynceotid);

property ResetSynceotid_2; @(posedge clk) (rst) != 1'b0 |->  count == reg_14 ;endproperty
assert property (ResetSynceotid_2);

endmodule