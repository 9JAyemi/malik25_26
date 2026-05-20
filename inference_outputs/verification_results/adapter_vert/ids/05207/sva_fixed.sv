module sync_reset_counter_sva (
    input logic clk,
    input logic count,
    input logic rst,
    input logic b0,
    input logic b1
);

property ResetSynceotid; @(posedge clk) (rst) |-> (count == 4'b0); endproperty
assert property (ResetSynceotid);

property ResetSynceotid_2; @(posedge clk) (rst) != 1'b1 |-> (count == count + 1); endproperty
assert property (ResetSynceotid_2);

endmodule