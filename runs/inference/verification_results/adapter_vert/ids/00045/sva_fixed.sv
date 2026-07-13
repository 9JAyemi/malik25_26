module top_module_sva (
    input logic a,
    input logic a_bitwise,
    input logic b,
    input logic b_bitwise,
    input logic cout,
    input logic out_not,
    input logic out_or_bitwise,
    input logic out_or_logical,
    input logic out_sum,
    input logic sum,
    input logic b1,
    input logic bxxxxxx,
    input logic clk_in_1
);

property SyncCheckeotid; @(posedge clk_in_1) (a) and (b) |-> cout == 1'b1 ;endproperty
assert property (SyncCheckeotid);

property SyncCheckeotid_2; @(posedge clk_in_1) (a) != (b) |-> sum == 1'b1 ;endproperty
assert property (SyncCheckeotid_2);

property ORSynceotid; @(posedge clk_in_1) (a_bitwise) |-> out_or_bitwise == (a_bitwise | b_bitwise) ;endproperty
assert property (ORSynceotid);

property ORSynceotid_2; @(posedge clk_in_1) (a_bitwise) && (b_bitwise) |-> out_or_logical == 1'b1 ;endproperty
assert property (ORSynceotid_2);

property NotSynceotid; @(posedge clk_in_1) (a_bitwise) || (b_bitwise) |-> out_not == 6'bxxxxxx ;endproperty
assert property (NotSynceotid);

property SyncCheckeotid_3; @(posedge clk_in_1) (a) and (b) |-> out_sum == (sum + out_or_bitwise) ;endproperty
assert property (SyncCheckeotid_3);

endmodule