module sky130_fd_sc_hvl__o21a_1_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic X,
    input logic a1_xored_a2,
    input logic b1_bit0,
    input logic clk_osc_19
);

property ClockSynceotid; @(posedge clk_osc_19) (A1) != (A2) |-> (X) == (a1_xored_a2 & B1); endproperty
assert property (ClockSynceotid);

property SyncCheckeotid; @(posedge clk_osc_19) (A1) && (A2) == (b1_bit0) ; endproperty
assert property (SyncCheckeotid);

endmodule