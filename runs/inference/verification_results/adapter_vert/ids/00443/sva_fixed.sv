module sky130_fd_sc_ls__o21a_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic X,
    input logic and0_out_X,
    input logic or0_out,
    input logic clock_div_15
);

property ClockSynceotid; @(posedge clock_div_15) (X) |-> (or0_out) && (and0_out_X); endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge clock_div_15) (or0_out) |-> (A2) || (A1); endproperty
assert property (ClockSynceotid_2);

property ClockSynceotid_3; @(posedge clock_div_15) (and0_out_X) |-> (or0_out) && (B1); endproperty
assert property (ClockSynceotid_3);

endmodule