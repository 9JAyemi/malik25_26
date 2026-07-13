module sky130_fd_sc_ls__o32ai_sva (
    input logic Y,
    input logic nor0_out,
    input logic nor1_out,
    input logic or0_out_Y,
    input logic b0,
    input logic b1,
    input logic clk_osc_15
);

property ClockSynceotid; @(posedge clk_osc_15) (Y) |-> (or0_out_Y == 1'b1) && (nor0_out == 1'b0) && (nor1_out == 1'b0) ;endproperty
assert property (ClockSynceotid);

property SyncSafeeotid; @(posedge clk_osc_15) (or0_out_Y) |-> (or0_out_Y == 1'b1) && (nor0_out == 1'b0) && (nor1_out == 1'b0) ;endproperty
assert property (SyncSafeeotid);

property SyncSafeeotid_2; @(posedge clk_osc_15) (or0_out_Y) |-> (or0_out_Y == 1'b1) && (nor0_out == 1'b0) && (nor1_out == 1'b0) ;endproperty
assert property (SyncSafeeotid_2);

property SyncSafeeotid_3; @(posedge clk_osc_15) (or0_out_Y) |-> (or0_out_Y == 1'b1) && (nor0_out == 1'b0) && (nor1_out == 1'b0) ;endproperty
assert property (SyncSafeeotid_3);

endmodule