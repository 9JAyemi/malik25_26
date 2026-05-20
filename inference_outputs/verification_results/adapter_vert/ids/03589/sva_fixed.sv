module addsub_sva (
    input logic ADD,
    input logic B,
    input logic B_INV,
    input logic COUT,
    input logic OUT,
    input logic SUB,
    input logic clk_in_1
);

property AddSynceotid; @(posedge clk_in_1) (B) |-> (B_INV) ;endproperty
assert property (AddSynceotid);

property AddOneeotid; @(posedge clk_in_1) (SUB) |-> (ADD) ;endproperty
assert property (AddOneeotid);

property ValidOuteotid; @(posedge clk_in_1) (SUB) |-> (OUT) ;endproperty
assert property (ValidOuteotid);

property ValidOuteotid_2; @(posedge clk_in_1) (SUB) |-> (COUT) ;endproperty
assert property (ValidOuteotid_2);

property SyncAddOneeotid; @(posedge clk_in_1) (B) != (B_INV) ;endproperty
assert property (SyncAddOneeotid);

property SyncAddOneeotid_2; @(posedge clk_in_1) (SUB) != (ADD) ;endproperty
assert property (SyncAddOneeotid_2);

property SyncAddOneeotid_3; @(posedge clk_in_1) (SUB) != (OUT) ;endproperty
assert property (SyncAddOneeotid_3);

property SyncAddOneeotid_4; @(posedge clk_in_1) (SUB) != (COUT) ;endproperty
assert property (SyncAddOneeotid_4);

endmodule