module sky130_fd_sc_hdll__o2bb2ai_sva (
    input logic Y,
    input logic nand0_out,
    input logic nand1_out_Y,
    input logic or0_out,
    input logic clk_osc_19
);

property ClockSynceotid; @(posedge clk_osc_19) (Y) |-> (nand0_out) && (or0_out) && (nand1_out_Y); endproperty
assert property (ClockSynceotid);

property SyncSafeeotid; @(posedge clk_osc_19) (Y) == (nand1_out_Y) ; endproperty
assert property (SyncSafeeotid);

property SyncSafeeotid_2; @(posedge clk_osc_19) (Y) |-> (nand0_out) && (or0_out) && (nand1_out_Y); endproperty
assert property (SyncSafeeotid_2);

endmodule