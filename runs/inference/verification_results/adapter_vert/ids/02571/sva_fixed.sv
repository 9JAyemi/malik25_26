module sky130_fd_sc_hdll__a22o_sva (
    input logic X,
    input logic and0_out,
    input logic and1_out,
    input logic or0_out_X,
    input logic clock_div_19
);

property ClockSynceotid; @(posedge clock_div_19) (X) |-> (and1_out) && (and0_out) && (or0_out_X); endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge clock_div_19) (X) |-> (and1_out) && (and0_out) && (or0_out_X); endproperty
assert property (ClockSynceotid_2);

property ClockSynceotid_3; @(posedge clock_div_19) (X) |-> (and1_out) && (and0_out) && (or0_out_X); endproperty
assert property (ClockSynceotid_3);

endmodule