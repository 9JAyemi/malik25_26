module ripple_adder_sva (
    input logic a,
    input logic b,
    input logic carry_out,
    input logic sum,
    input logic clk_reset_19
);

property ResetSynceotid; @(negedge clk_reset_19) (a) |-> (sum) ;endproperty
assert property (ResetSynceotid);

property ResetSynceotid_2; @(negedge clk_reset_19) (b) |-> (sum) ;endproperty
assert property (ResetSynceotid_2);

property ResetSynceotid_3; @(negedge clk_reset_19) (a) && @(negedge clk_reset_19) (b) |-> (carry_out) ;endproperty
assert property (ResetSynceotid_3);

property ResetSynceotid_4; @(negedge clk_reset_19) (a) && @(negedge clk_reset_19) (b) &&  (  !(a) && !(b)  ) |-> !(carry_out) ;endproperty
assert property (ResetSynceotid_4);

endmodule