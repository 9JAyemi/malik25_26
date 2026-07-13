module sky130_fd_sc_ms__a211o_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic X,
    input logic and0_out,
    input logic or0_out_X,
    input logic clock_div_19
);

property ClockSynceotid; @(posedge clock_div_19) (X) |-> (and0_out) && (or0_out_X); endproperty
assert property (ClockSynceotid);

property ValidSynceotid; @(posedge clock_div_19) (and0_out) &&  (  (A1) && (A2)  ) ; endproperty
assert property (ValidSynceotid);

property ValidSynceotid_2; @(posedge clock_div_19) (or0_out_X) |->  (  (and0_out) && (C1) || (B1)  ) ; endproperty
assert property (ValidSynceotid_2);

property ClockSynceotid_2; @(posedge clock_div_19) (X) == (or0_out_X) ; endproperty
assert property (ClockSynceotid_2);

endmodule