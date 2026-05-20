module counter_mod_rtl_sva (
    input logic carry,
    input logic clk,
    input logic q,
    input logic rst,
    input logic up_down,
    input logic b0,
    input logic b0000,
    input logic b1,
    input logic b1111
);

property ResetSynceotid; @(posedge clk) (rst) |-> (q == 4'b0) && (carry == 1'b0) ;endproperty
assert property (ResetSynceotid);

property SyncUpeotid; @(posedge clk) (rst) != 1'b1 &&  (up_down == 1'b0)  |->  (q == 4'b1111) &&  (carry == 1'b1)  ;endproperty
assert property (SyncUpeotid);

property SyncDowneotid; @(posedge clk) (rst) != 1'b1 &&  (up_down != 1'b0)  |->  (q == 4'b0000) &&  (carry == 1'b1)  ;endproperty
assert property (SyncDowneotid);

property SyncCtrleotid; @(posedge clk) (rst) != 1'b1 &&  (up_down != 1'b0)  &&  (q != 4'b0000)  |->  (q == 4'b1111) ;endproperty
assert property (SyncCtrleotid);

property SyncDowneotid_2; @(posedge clk) (rst) != 1'b1 &&  (up_down == 1'b0)  &&  (q != 4'b1111)  |->  (q == 4'b0000) ;endproperty
assert property (SyncDowneotid_2);

endmodule