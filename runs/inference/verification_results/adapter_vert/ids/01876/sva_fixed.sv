module sky130_fd_sc_lp__a21boi_sva (
    input logic A1,
    input logic A2,
    input logic Y,
    input logic and0_out,
    input logic b,
    input logic nor0_out_Y,
    input logic clk_osc_19
);

property ClockSynceotid; @(posedge clk_osc_19) (Y) |-> (b) ;endproperty
assert property (ClockSynceotid);

property SyncCheckeotid; @(posedge clk_osc_19) (and0_out) |-> (and0_out) && (A1) && (A2) ;endproperty
assert property (SyncCheckeotid);

property ClockSynceotid_2; @(posedge clk_osc_19) (nor0_out_Y) |-> ! (b) || ! (and0_out) ;endproperty
assert property (ClockSynceotid_2);

property ClockSynceotid_3; @(posedge clk_osc_19) (Y) |-> (nor0_out_Y) ;endproperty
assert property (ClockSynceotid_3);

endmodule