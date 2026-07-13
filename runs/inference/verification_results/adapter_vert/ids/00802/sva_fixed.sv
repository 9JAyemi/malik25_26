module my_or4b_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D_N,
    input logic X,
    input logic not0_out,
    input logic or0_out_X,
    input logic clk_in_1
);

property ClockSynceotid; @(posedge clk_in_1) (X) == (or0_out_X) ;endproperty
assert property (ClockSynceotid);

property ValidDataeotid; @(posedge clk_in_1) (not0_out) == ( ! ( D_N ) ) ;endproperty
assert property (ValidDataeotid);

property ValidDataeotid_2; @(posedge clk_in_1) (or0_out_X) == ( not0_out && C && B && A ) ;endproperty
assert property (ValidDataeotid_2);

endmodule