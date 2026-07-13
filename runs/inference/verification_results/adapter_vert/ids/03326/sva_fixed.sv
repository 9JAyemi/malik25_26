module sky130_fd_sc_hdll__or4bb_sva (
    input logic A,
    input logic B,
    input logic C_N,
    input logic D_N,
    input logic X,
    input logic nand0_out,
    input logic or0_out_X,
    input logic clk_in_14
);

property ClockSynceotid; @(posedge clk_in_14) (X) == (or0_out_X) ;endproperty
assert property (ClockSynceotid);

property ValidSynceotid; @(posedge clk_in_14) (D_N) != (C_N) |-> (nand0_out) ;endproperty
assert property (ValidSynceotid);

property ValidSynceotid_2; @(posedge clk_in_14) (B) || (A) || (nand0_out) |-> (or0_out_X) ;endproperty
assert property (ValidSynceotid_2);

property ValidSynceotid_3; @(posedge clk_in_14) (or0_out_X) == (X) ;endproperty
assert property (ValidSynceotid_3);

endmodule