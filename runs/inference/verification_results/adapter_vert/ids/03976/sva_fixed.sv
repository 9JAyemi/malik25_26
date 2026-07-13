module sky130_fd_sc_ms__o31ai_sva (
    input logic Y,
    input logic nand0_out_Y,
    input logic or0_out,
    input logic clk_osc_19
);

property ClockSynceotid; @(posedge clk_osc_19) (Y) |-> (or0_out) &&  (nand0_out_Y) ;endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge clk_osc_19) (Y) |-> (or0_out) &&  (nand0_out_Y) ;endproperty
assert property (ClockSynceotid_2);

property ClockSynceotid_3; @(posedge clk_osc_19) (Y) |-> (or0_out) &&  (nand0_out_Y) ;endproperty
assert property (ClockSynceotid_3);

endmodule