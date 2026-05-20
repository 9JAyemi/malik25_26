module sky130_fd_sc_hd__a211oi_sva (
    input logic Y,
    input logic and0_out,
    input logic nor0_out_Y,
    input logic clk_osc_19
);

property ClockSynceotid; @(posedge clk_osc_19) (Y) |-> (and0_out) && !(nor0_out_Y) ;endproperty
assert property (ClockSynceotid);

property SyncCheckeotid; @(posedge clk_osc_19) (and0_out) &&  (  !(and0_out)  &&  (nor0_out_Y)  ) |-> (Y) ;endproperty
assert property (SyncCheckeotid);

property SyncCheckeotid_2; @(posedge clk_osc_19) (and0_out) &&  (  (and0_out)  &&  !(nor0_out_Y)  ) |-> (Y) ;endproperty
assert property (SyncCheckeotid_2);

endmodule