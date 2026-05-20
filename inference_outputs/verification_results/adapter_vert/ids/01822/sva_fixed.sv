module sky130_fd_sc_ms__o211ai_sva (
    input logic Y,
    input logic nand0_out_Y,
    input logic or0_out,
    input logic clk_osc_14
);

property ClockSynceotid; @(posedge clk_osc_14) (Y) |-> (or0_out) && !(nand0_out_Y) ;endproperty
assert property (ClockSynceotid);

property SyncSafeeotid; @(posedge clk_osc_14) (or0_out) &&  (nand0_out_Y) |-> (Y) ;endproperty
assert property (SyncSafeeotid);

property SyncSafeeotid_2; @(posedge clk_osc_14) (or0_out) &&  !(nand0_out_Y)  |-> !(Y) ;endproperty
assert property (SyncSafeeotid_2);

endmodule