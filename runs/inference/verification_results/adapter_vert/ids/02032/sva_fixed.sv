module sky130_fd_sc_ms__o21ai_sva (
    input logic B1,
    input logic nand0_out_Y,
    input logic or0_out,
    input logic clk_osc_19
);

property ClockSynceotid; @(posedge clk_osc_19) (or0_out) |-> (nand0_out_Y); endproperty
assert property (ClockSynceotid);

property SyncCheckeotid; @(posedge clk_osc_19) (or0_out) &&  (  (B1) &&  (or0_out)  ) |-> (nand0_out_Y) ; endproperty
assert property (SyncCheckeotid);

property SyncSafeeotid; @(posedge clk_osc_19) (or0_out) &&  (  (B1) &&  !(or0_out)  ) |-> !(nand0_out_Y) ; endproperty
assert property (SyncSafeeotid);

endmodule