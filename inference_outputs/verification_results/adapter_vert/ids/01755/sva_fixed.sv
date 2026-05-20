module top_module_sva (
    input logic cin1,
    input logic clk,
    input logic cout1,
    input logic d1,
    input logic d2,
    input logic q,
    input logic q1,
    input logic reset,
    input logic select,
    input logic sum1,
    input logic b0,
    input logic cin2,
    input logic cout2,
    input logic q2,
    input logic sum2
);

property ResetSynceotid; @(posedge clk) (reset) |-> q == 0 ;endproperty
assert property (ResetSynceotid);

property ResetSynceotid_2; @(posedge clk) (reset) |-> (q1) == 0 && (q2) == 0 && (cin1) == 0 && (cin2) == 0 ;endproperty
assert property (ResetSynceotid_2);

property SyncCheckeotid; @(posedge clk) ( !reset ) &&  (  select ) |-> q == sum1 ;endproperty
assert property (SyncCheckeotid);

property SyncCheckeotid_2; @(posedge clk) ( !reset ) &&  ( !select ) |-> q == sum2 ;endproperty
assert property (SyncCheckeotid_2);

property SyncCheckeotid_3; @(posedge clk) ( !reset ) &&  (  select ) |-> (q1) == d1 && (cin1) == 1'b0 && (q2) == sum1 && (cin2) == cout1 ;endproperty
assert property (SyncCheckeotid_3);

property SyncCheckeotid_4; @(posedge clk) ( !reset ) &&  ( !select ) |-> (q2) == d2 && (cin2) == 1'b0 && (q1) == sum2 && (cin1) == cout2 ;endproperty
assert property (SyncCheckeotid_4);

endmodule