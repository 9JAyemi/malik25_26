module sky130_fd_sc_hvl__a22oi_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic Y,
    input logic and0_out_Y,
    input logic nand0_out,
    input logic nand1_out,
    input logic clk_osc_19
);

property ClockSynceotid; @(posedge clk_osc_19) (Y) |-> (nand0_out == (A2 && A1)) && (nand1_out == (B2 && B1)) && (and0_out_Y == (nand0_out && nand1_out)) ;endproperty
assert property (ClockSynceotid);

property SyncCheckeotid; @(posedge clk_osc_19) (Y) |-> (nand0_out == (A2 && A1)) && (nand1_out == (B2 && B1)) && (and0_out_Y == (nand0_out && nand1_out)) ;endproperty
assert property (SyncCheckeotid);

property SyncCheckeotid_2; @(posedge clk_osc_19) (Y) |-> (nand0_out == (A2 && A1)) && (nand1_out == (B2 && B1)) && (and0_out_Y == (nand0_out && nand1_out)) ;endproperty
assert property (SyncCheckeotid_2);

endmodule