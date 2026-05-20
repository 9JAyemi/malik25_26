module sky130_fd_sc_ls__a32oi_sva (
    input logic Y,
    input logic and0_out_Y,
    input logic nand0_out,
    input logic nand1_out,
    input logic b1,
    input logic clock_div_19
);

property ClockSynceotid; @(posedge clock_div_19) (Y) |-> (nand0_out) && (nand1_out) && (and0_out_Y); endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge clock_div_19) (Y) == (1'b1) |-> (nand0_out) && (nand1_out) && (and0_out_Y); endproperty
assert property (ClockSynceotid_2);

property ClockSynceotid_3; @(posedge clock_div_19) (Y) != 1'b1  |->  !( (nand0_out) && (nand1_out) && (and0_out_Y) ) ; endproperty
assert property (ClockSynceotid_3);

endmodule