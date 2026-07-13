module sky130_fd_sc_hvl__lsbuflv2hv_clkiso_hlkg_sva (
    input logic A,
    input logic SLEEP,
    input logic SLEEP_B,
    input logic X,
    input logic and0_out_X,
    input logic clk_osc_17
);

property WakeUpeotid; @(posedge clk_osc_17) (X) |-> (SLEEP) != (A); endproperty
assert property (WakeUpeotid);

property WakeUpeotid_2; @(posedge clk_osc_17) (X) |-> (and0_out_X) && (SLEEP_B); endproperty
assert property (WakeUpeotid_2);

property ClockSynceotid; @(posedge clk_osc_17) (X) == (and0_out_X) &&  ( (SLEEP) != (A) ); endproperty
assert property (ClockSynceotid);

endmodule