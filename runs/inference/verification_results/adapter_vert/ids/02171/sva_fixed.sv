module sky130_fd_sc_ls__a222o_sva (
    input logic A1,
    input logic A2,
    input logic C1,
    input logic C2,
    input logic X,
    input logic and0_out,
    input logic and1_out,
    input logic and2_out,
    input logic or0_out_X,
    input logic clk_osc_19
);

property ClockSynceotid; @(posedge clk_osc_19) (X) |-> (or0_out_X); endproperty
assert property (ClockSynceotid);

property SyncCheckeotid; @(posedge clk_osc_19) (and1_out) &&  ( (A1) &&  (A2) ) |->  (and0_out) ; endproperty
assert property (SyncCheckeotid);

property SyncCheckeotid_2; @(posedge clk_osc_19) (and2_out) &&  ( (C1) &&  (C2) ) |->  (and0_out) ; endproperty
assert property (SyncCheckeotid_2);

property SyncSafeeotid; @(posedge clk_osc_19) (or0_out_X) |->  (and1_out) &&  (and0_out) &&  (and2_out) ; endproperty
assert property (SyncSafeeotid);

endmodule