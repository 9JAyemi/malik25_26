module sky130_fd_sc_lp__o31ai_sva (
    input logic B1,
    input logic Y,
    input logic nand0_out,
    input logic or0_out,
    input logic clk_osc_18
);

property ClockSynceotid; @(posedge clk_osc_18) (Y) |-> (or0_out) ;endproperty
assert property (ClockSynceotid);

property SyncSafeeotid; @(posedge clk_osc_18) (or0_out) &&  (  (B1) &&  (or0_out) &&  (nand0_out)  ) |-> (nand0_out) ;endproperty
assert property (SyncSafeeotid);

property ClockSynceotid_2; @(posedge clk_osc_18) (nand0_out) &&  (  (B1) &&  (or0_out) &&  (nand0_out)  ) |-> (Y) ;endproperty
assert property (ClockSynceotid_2);

endmodule