module sky130_fd_sc_ms__nand2b_sva (
    input logic A_N,
    input logic B,
    input logic Y,
    input logic not0_out,
    input logic or0_out_Y,
    input logic b1,
    input logic clock_div_19
);

property ClockSynceotid; @(posedge clock_div_19) (Y) |-> (or0_out_Y == (not0_out && A_N)); endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge clock_div_19) (or0_out_Y) |-> (Y == (or0_out_Y)); endproperty
assert property (ClockSynceotid_2);

property ClockSynceotid_3; @(posedge clock_div_19) (not0_out) == (1'b1) &&  (B) |->  (or0_out_Y) ; endproperty
assert property (ClockSynceotid_3);

endmodule