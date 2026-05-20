module sky130_fd_sc_ls__clkinv_sva (
    input logic A,
    input logic Y,
    input logic not0_out_Y,
    input logic b0,
    input logic b1,
    input logic clock_div_19
);

property ClockSynceotid; @(posedge clock_div_19) (Y) |-> (not0_out_Y) ;endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge clock_div_19) (not0_out_Y) == (1'b1) &&  (  A  != 1'b1  ) |->  (Y) != 1'b1 ;endproperty
assert property (ClockSynceotid_2);

property ClockSynceotid_3; @(posedge clock_div_19) (not0_out_Y) != 1'b1  &&  (  A  != 1'b1  ) |->  (Y) != 1'b1 ;endproperty
assert property (ClockSynceotid_3);

property ClockSynceotid_4; @(posedge clock_div_19) (not0_out_Y) != 1'b1  &&  (  A  == 1'b1  ) |->  (Y) == 1'b0 ;endproperty
assert property (ClockSynceotid_4);

endmodule