module sky130_fd_sc_hd__o2bb2a_sva (
    input logic X,
    input logic and0_out_X,
    input logic nand0_out,
    input logic or0_out,
    input logic b1,
    input logic clk_osc_17
);

property ClockSynceotid; @(posedge clk_osc_17) (X) |-> (nand0_out == 1'b1) && (or0_out == 1'b1) && (and0_out_X == 1'b1); endproperty
assert property (ClockSynceotid);

property SyncSafeeotid; @(posedge clk_osc_17) (X) |-> (nand0_out == 1'b1) && (or0_out == 1'b1) && (and0_out_X == 1'b1); endproperty
assert property (SyncSafeeotid);

property SyncSafeeotid_2; @(posedge clk_osc_17) (X) |-> (nand0_out == 1'b1) && (or0_out == 1'b1) && (and0_out_X == 1'b1); endproperty
assert property (SyncSafeeotid_2);

endmodule