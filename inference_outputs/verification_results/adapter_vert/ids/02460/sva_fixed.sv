module sky130_fd_sc_ls__o2111a_sva (
    input logic X,
    input logic and0_out_X,
    input logic or0_out,
    input logic clock_div_15
);

property ClockSynceotid; @(posedge clock_div_15) (X) |-> (or0_out) ;endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge clock_div_15) (X) |-> (and0_out_X) ;endproperty
assert property (ClockSynceotid_2);

property ClockSynceotid_3; @(posedge clock_div_15) (X) == (and0_out_X) ;endproperty
assert property (ClockSynceotid_3);

endmodule