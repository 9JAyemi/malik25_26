module and_or_module_sva (
    input logic a,
    input logic b,
    input logic g_out,
    input logic p_out,
    input logic clk_in_1
);

property SyncAndeotid; @(posedge clk_in_1) (a) && (b) |-> (g_out) ;endproperty
assert property (SyncAndeotid);

property SyncOreotid; @(posedge clk_in_1) (a) || (b) |-> (p_out) ;endproperty
assert property (SyncOreotid);

endmodule