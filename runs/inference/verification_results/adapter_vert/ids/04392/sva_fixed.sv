module my_module_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1,
    input logic VGND,
    input logic VPB,
    input logic VPWR,
    input logic X,
    input logic b1,
    input logic clk_osc_19
);

property ClockSynceotid; @(posedge clk_osc_19) (A1) == (B1) && (A2) == (B2) |-> (X) == 1'b1 ;endproperty
assert property (ClockSynceotid);

property SyncCheckeotid; @(posedge clk_osc_19) (C1) == (VPWR) && (VPB) == (VGND) |-> (X) != 1'b1 ;endproperty
assert property (SyncCheckeotid);

endmodule