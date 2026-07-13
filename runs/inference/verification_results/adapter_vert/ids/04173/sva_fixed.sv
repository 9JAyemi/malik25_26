module logic_module_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic X,
    input logic clk_osc_18
);

property ClockSynceotid; @(posedge clk_osc_18) (A1 | A2) & (~B1 | B2) & (~A1 | ~A2 | B1) |-> X ;endproperty
assert property (ClockSynceotid);

property SyncCheckeotid; @(posedge clk_osc_18) (A1 | A2) & (~B1 | B2) & (~A1 | ~A2 | B1) |-> X ;endproperty
assert property (SyncCheckeotid);

property SyncSafeeotid; @(posedge clk_osc_18) (A1 | A2) & (~B1 | B2) & (~A1 | ~A2 | B1) |-> X ;endproperty
assert property (SyncSafeeotid);

endmodule