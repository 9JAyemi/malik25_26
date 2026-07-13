module sky130_fd_sc_hd__o221ai_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1,
    input logic Y,
    input logic nand0_out_Y,
    input logic or0_out,
    input logic or1_out,
    input logic b0,
    input logic b1,
    input logic clk_in_18
);

property ClockSynceotid; @(posedge clk_in_18) (Y) |-> (or0_out == 1'b1) && (or1_out == 1'b1) && (nand0_out_Y == 1'b0); endproperty
assert property (ClockSynceotid);

property SyncCheckeotid; @(posedge clk_in_18) (or0_out) |-> (B2 == 1'b1) && (B1 == 1'b1); endproperty
assert property (SyncCheckeotid);

property SyncCheckeotid_2; @(posedge clk_in_18) (or1_out) |-> (A2 == 1'b1) && (A1 == 1'b1); endproperty
assert property (SyncCheckeotid_2);

property SyncSafeeotid; @(posedge clk_in_18) (nand0_out_Y) |-> (or1_out == 1'b1) && (or0_out == 1'b1) && (C1 == 1'b0); endproperty
assert property (SyncSafeeotid);

property SyncSafeeotid_2; @(posedge clk_in_18) (Y) |-> (nand0_out_Y == 1'b0); endproperty
assert property (SyncSafeeotid_2);

endmodule