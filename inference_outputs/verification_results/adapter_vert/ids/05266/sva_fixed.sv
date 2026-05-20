module top_module_sva (
    input logic a,
    input logic b,
    input logic c,
    input logic d,
    input logic max,
    input logic clk_in_1
);

property MaxSynceotid; @(posedge clk_in_1) (a) > (b) |-> (max) == (a) ; endproperty
assert property (MaxSynceotid);

property SyncEqeotid; @(posedge clk_in_1) (c) > (d) |-> (max) == (c) ; endproperty
assert property (SyncEqeotid);

property SyncCheckeotid; @(posedge clk_in_1) (a) <= (b) && (c) <= (d) |-> (max) == (d) ; endproperty
assert property (SyncCheckeotid);

endmodule