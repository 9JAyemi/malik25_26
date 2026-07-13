module gray_counter_sva (
    input logic clk,
    input logic counter_out,
    input logic enable,
    input logic gray_out,
    input logic q,
    input logic reset,
    input logic up_down,
    input logic b0,
    input logic b00,
    input logic b00000000,
    input logic b0100000,
    input logic b1,
    input logic b1000000
);

property ResetSynceotid; @(posedge clk) (reset) |-> (counter_out) == (2'b0); endproperty
assert property (ResetSynceotid);

property ResetSynceotid_2; @(posedge clk) (reset) |-> (gray_out) == (2'b00); endproperty
assert property (ResetSynceotid_2);

property ResetSynceotid_3; @(posedge clk) (reset) |-> (q) == (8'b00000000); endproperty
assert property (ResetSynceotid_3);

property SyncCtrleotid; @(posedge clk) ( !reset ) && (  enable ) && (  up_down ) |-> (counter_out) == (counter_out + 2'b1); endproperty
assert property (SyncCtrleotid);

property SyncCtrleotid_2; @(posedge clk) ( !reset ) && (  enable ) && ! (  up_down )  |-> (counter_out) == (counter_out - 2'b1); endproperty
assert property (SyncCtrleotid_2);

property SyncCtrleotid_3; @(posedge clk) ( !reset ) &&  (  enable  &&  (  up_down  !=  7'b0100000  &&  up_down  !=  7'b1000000 )  ) |-> (gray_out) == (counter_out); endproperty
assert property (SyncCtrleotid_3);

property SyncCtrleotid_4; @(posedge clk) ( !reset ) &&  (  enable  &&  (  up_down  !=  7'b0100000  &&  up_down  !=  7'b1000000 )  ) |-> (q) == ({gray_out, counter_out}); endproperty
assert property (SyncCtrleotid_4);

endmodule