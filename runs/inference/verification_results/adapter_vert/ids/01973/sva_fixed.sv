module sky130_fd_sc_lp__o31a_sva (
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic X,
    input logic and0_out_X,
    input logic or0_out,
    input logic clk_osc_19
);

property ClockSynceotid; @(posedge clk_osc_19) (X) |-> (or0_out) && (and0_out_X); endproperty
assert property (ClockSynceotid);

property SyncCheckeotid; @(posedge clk_osc_19) (or0_out) &&  (  (A2) || (A1) || (A3)  ) ; endproperty
assert property (SyncCheckeotid);

property SyncSafeeotid; @(posedge clk_osc_19) (and0_out_X) |->  (  (or0_out)  && (  (B1)  )  ) ; endproperty
assert property (SyncSafeeotid);

property SyncSafeeotid_2; @(posedge clk_osc_19) (X) == (and0_out_X) ; endproperty
assert property (SyncSafeeotid_2);

endmodule