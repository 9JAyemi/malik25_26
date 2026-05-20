module counter4_sva (
    input logic clk,
    input logic count,
    input logic rst,
    input logic b0000,
    input logic b1,
    input logic b1001
);

property ResetSynceotid; @(posedge clk) (rst) |-> count == 4'b0000 ;endproperty
assert property (ResetSynceotid);

property SyncCheckeotid; @(posedge clk) (rst) != 1'b1 &&  (count) != 4'b1001  |->  (count) == (count + 1) ;endproperty
assert property (SyncCheckeotid);

property ResetSynceotid_2; @(posedge clk) (rst) != 1'b1 &&  (count) == 4'b1001  |->  (count) == 4'b0000 ;endproperty
assert property (ResetSynceotid_2);

endmodule