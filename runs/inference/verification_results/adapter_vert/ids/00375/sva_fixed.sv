module sky130_fd_sc_hd__o211a_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic X,
    input logic and0_out_X,
    input logic or0_out,
    input logic clk_osc_13
);

property ClockSynceotid; @(posedge clk_osc_13) (X) |-> (or0_out) && (and0_out_X); endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge clk_osc_13) (or0_out) &&  (  (A2) || (A1)  ) ; endproperty
assert property (ClockSynceotid_2);

property SyncSafeeotid; @(posedge clk_osc_13) (and0_out_X) |->  (  (or0_out) && (B1) && (C1)  ) ; endproperty
assert property (SyncSafeeotid);

property ClockSynceotid_3; @(posedge clk_osc_13) (X) == (and0_out_X) ; endproperty
assert property (ClockSynceotid_3);

endmodule