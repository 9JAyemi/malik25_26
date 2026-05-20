module sky130_fd_sc_lp__a311oi_sva (
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic C1,
    input logic Y,
    input logic and0_out,
    input logic nor0_out_Y,
    input logic b1,
    input logic clock_div_14
);

property ClockSynceotid; @(posedge clock_div_14) (and0_out) |-> (A3 == 1'b1) && (A1 == 1'b1) && (A2 == 1'b1); endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge clock_div_14) (nor0_out_Y) |-> (and0_out != 1'b1) || (B1 != 1'b1) || (C1 != 1'b1); endproperty
assert property (ClockSynceotid_2);

property ClockSynceotid_3; @(posedge clock_div_14) (Y) == (nor0_out_Y); endproperty
assert property (ClockSynceotid_3);

endmodule