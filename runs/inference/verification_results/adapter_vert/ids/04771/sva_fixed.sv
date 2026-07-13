module sky130_fd_sc_lp__a21oi_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic Y,
    input logic and0_out,
    input logic nor0_out_Y,
    input logic clk_osc_19
);

property ClockSynceotid; @(posedge clk_osc_19) (Y) |-> (and0_out) && !(nor0_out_Y) ;endproperty
assert property (ClockSynceotid);

property SyncCheckeotid; @(posedge clk_osc_19) (and0_out) &&  (  !(B1)  &&  (A1)  &&  (A2)  ) ;endproperty
assert property (SyncCheckeotid);

property SyncSafeeotid; @(posedge clk_osc_19) (nor0_out_Y) |->  (  !(B1)  &&  (A1)  &&  (A2)  ) ;endproperty
assert property (SyncSafeeotid);

property SyncSafeeotid_2; @(posedge clk_osc_19) (Y) |->  (  !(B1)  &&  (A1)  &&  (A2)  ) ;endproperty
assert property (SyncSafeeotid_2);

endmodule