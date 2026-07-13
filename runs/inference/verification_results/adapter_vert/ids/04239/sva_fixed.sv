module sky130_fd_sc_hd__xor2_sva (
    input logic A,
    input logic B,
    input logic X,
    input logic xor0_out_X,
    input logic clk_in_14
);

property ClockXorSynceotid; @(posedge clk_in_14) (X) |-> (xor0_out_X == (B ^ A)) ;endproperty
assert property (ClockXorSynceotid);

property ClockSynceotid; @(posedge clk_in_14) (X) |-> (xor0_out_X == (B ^ A)) ;endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge clk_in_14) (X) |-> (xor0_out_X == (B ^ A)) ;endproperty
assert property (ClockSynceotid_2);

endmodule