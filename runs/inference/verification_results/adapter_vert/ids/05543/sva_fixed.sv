module sky130_fd_sc_ls__clkdlyinv3sd1_sva (
    input logic A,
    input logic Y,
    input logic not0_out_Y,
    input logic b1,
    input logic clk_in_14
);

property ClockSynceotid; @(posedge clk_in_14) (Y) |-> (not0_out_Y) ;endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge clk_in_14) (A) |-> (not0_out_Y) ;endproperty
assert property (ClockSynceotid_2);

property ClockSynceotid_3; @(posedge clk_in_14) (not0_out_Y) == (1'b1) &&  ( (A) ) |-> (Y) == (1'b1) ;endproperty
assert property (ClockSynceotid_3);

property ClockSynceotid_4; @(posedge clk_in_14) (not0_out_Y) != 1'b1  &&  ( (A) ) |-> (Y) != 1'b1 ;endproperty
assert property (ClockSynceotid_4);

endmodule