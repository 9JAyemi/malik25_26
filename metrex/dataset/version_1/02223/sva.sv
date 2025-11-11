// SVA checker for ripple_adder
// Bind this file to the DUT; concise but high-value assertions and coverage.

`ifndef RIPPLE_ADDER_SVA
`define RIPPLE_ADDER_SVA

bind ripple_adder ripple_adder_sva sva_i(.*);

module ripple_adder_sva (
  input logic        clk,
  input logic [3:0]  a, b,
  input logic [4:0]  sum,
  input logic [3:0]  a_reg, b_reg, carry_reg
);
  default clocking cb @(posedge clk); endclocking

  // history valid after first clock
  logic hist_vld;
  always_ff @(posedge clk) hist_vld <= 1'b1;

  // 1) Pipeline sampling checks
  ap_sample: assert property (hist_vld |-> (a_reg == $past(a) && b_reg == $past(b)));

  // 2) Functional correctness: 1-cycle latency, carry-in = 0
  ap_sum:    assert property (hist_vld |-> (sum === ($past({1'b0,a}) + $past({1'b0,b}))));

  // 3) Bit-level sanity: LSB ignores carry-in; MSB equals carry-out
  ap_lsb:    assert property (hist_vld |-> (sum[0] == ($past(a[0]) ^ $past(b[0]))));
  ap_msb:    assert property (hist_vld |-> (sum[4] == (($past(a[3]) & $past(b[3])) |
                                                      (($past(a[3]) ^ $past(b[3])) & ($past(a[2]) & $past(b[2]))) |
                                                      (($past(a[3]) ^ $past(b[3])) & ($past(a[2]) ^ $past(b[2])) & ($past(a[1]) & $past(b[1]))) |
                                                      (($past(a[3]) ^ $past(b[3])) & ($past(a[2]) ^ $past(b[2])) & ($past(a[1]) ^ $past(b[1])) & ($past(a[0]) & $past(b[0]))))));

  // 4) Internal carry chain must match expected ripple (exposes incorrect carry use)
  ap_c0:     assert property (hist_vld |-> (carry_reg[0] == ($past(a[0]) & $past(b[0]))));
  ap_c1:     assert property (hist_vld |-> (carry_reg[1] ==
                               (($past(a[1]) & $past(b[1])) |
                                (($past(a[1]) ^ $past(b[1])) & ($past(a[0]) & $past(b[0]))))));
  ap_c2:     assert property (hist_vld |-> (carry_reg[2] ==
                               (($past(a[2]) & $past(b[2])) |
                                (($past(a[2]) ^ $past(b[2])) & ($past(a[1]) & $past(b[1]))) |
                                (($past(a[2]) ^ $past(b[2])) & ($past(a[1]) ^ $past(b[1])) & ($past(a[0]) & $past(b[0]))))));

  // 5) No X on output once history is valid
  ap_no_x:   assert property (hist_vld |-> !$isunknown(sum));

  // Coverage: key corner cases
  cp_zero:      cover property (hist_vld && $past(a)==4'h0 && $past(b)==4'h0 && sum==5'd0);
  cp_max:       cover property (hist_vld && $past(a)==4'hF && $past(b)==4'hF && sum==5'd30);   // 15+15
  cp_fullprop:  cover property (hist_vld && $past(a)==4'hF && $past(b)==4'h1 && sum==5'd16);   // full carry propagate
  cp_nocarry:   cover property (hist_vld && sum[4]==1'b0);                                     // any no-carry case

endmodule

`endif