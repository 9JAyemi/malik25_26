module sky130_fd_sc_hvl__a22o_sva (
    input logic X,
    input logic and0_out,
    input logic and1_out,
    input logic or0_out_X,
    input logic b1,
    input logic clk_osc_19
);

property ClockSynceotid; @(posedge clk_osc_19) (X) |-> (and1_out) && (and0_out) && (or0_out_X); endproperty
assert property (ClockSynceotid);

property SyncCheckeotid; @(posedge clk_osc_19) (and1_out) && (and0_out) == (1'b1) |-> (or0_out_X) ; endproperty
assert property (SyncCheckeotid);

property SyncSafeeotid; @(posedge clk_osc_19) (and1_out) && (and0_out) && (or0_out_X) |-> (X) ; endproperty
assert property (SyncSafeeotid);

endmodule