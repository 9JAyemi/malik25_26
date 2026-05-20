module top_module_sva (
    input logic a,
    input logic b,
    input logic clk,
    input logic sub,
    input logic sum1,
    input logic sum2,
    input logic xor_b
);

property SyncAddOneeotid; @(posedge clk) (a) |-> (sum1) ;endproperty
assert property (SyncAddOneeotid);

property SyncAddOneeotid_2; @(posedge clk) (a) &&  (b) &&  (sub) |-> (sum2) ;endproperty
assert property (SyncAddOneeotid_2);

property SyncXorCheckeotid; @(posedge clk) (a) &&  (b) &&  (sub) |-> (xor_b) ;endproperty
assert property (SyncXorCheckeotid);

property SyncAddOneeotid_3; @(posedge clk) (a) &&  (b) &&  (sub) |-> (sum2) ;endproperty
assert property (SyncAddOneeotid_3);

endmodule