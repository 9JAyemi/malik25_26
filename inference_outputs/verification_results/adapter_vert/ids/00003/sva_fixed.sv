module sky130_fd_sc_hd__o21bai_sva (
    input logic A1,
    input logic A2,
    input logic B1_N,
    input logic Y,
    input logic b,
    input logic nand0_out_Y,
    input logic or0_out,
    input logic clk_osc_18
);

property ClockSynceotid; @(posedge clk_osc_18) (B1_N) |->  (b) ;endproperty
assert property (ClockSynceotid);

property SyncOkeotid; @(posedge clk_osc_18) (A2) ||  (A1) |->  (or0_out) ;endproperty
assert property (SyncOkeotid);

property SyncSafeeotid; @(posedge clk_osc_18) (B1_N) &&  (A2) &&  (A1) |->  (nand0_out_Y) ;endproperty
assert property (SyncSafeeotid);

property SyncSafeeotid_2; @(posedge clk_osc_18) (B1_N) &&  (A2) &&  (A1) |->  (Y) ;endproperty
assert property (SyncSafeeotid_2);

endmodule