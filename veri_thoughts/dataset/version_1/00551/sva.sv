// SVA for detect_0_to_1
// Bind this file to the DUT

module detect_0_to_1_sva #(parameter W=32)
(
  input  logic              clk,
  input  logic              reset,
  input  logic [W-1:0]      in,
  input  logic [W-1:0]      out,
  input  logic [W-1:0]      prev_in
);

  default clocking cb @(posedge clk); endclocking

  // Reset behavior
  a_reset_clears:    assert property (reset |-> (out == '0 && prev_in == '0));

  // prev_in update rules
  a_prev_updates:    assert property ((!reset && !$past(reset)) |-> (prev_in == $past(in)));
  a_prev_after_rst:  assert property ((!reset &&  $past(reset)) |-> (prev_in == in));

  // Functional correctness of out (0->1 edge detect)
  a_out_func_run:    assert property ((!reset && !$past(reset)) |-> (out == (in & ~ $past(in))));
  a_out_func_postR:  assert property ((!reset &&  $past(reset)) |-> (out == in));

  // Safety properties
  a_out_subset_in:   assert property ((out & ~in) == '0);                  // out ⊆ in
  a_out_no_old_ones: assert property ((!reset && !$past(reset)) |-> ((out & $past(in)) == '0)); // no 1s where past in was 1
  a_one_cycle_pulse: assert property ((!reset && !$past(reset)) |-> ((out & $past(out)) == '0)); // no consecutive pulses

  // Coverage
  c_post_reset_det:  cover  property (!reset && $past(reset) && (in != '0) && (out == in));
  c_any_detect:      cover  property (!reset && !$past(reset) && (out != '0));
  c_multi_bit:       cover  property (!reset && !$past(reset) && ($countones(out) >= 2));
  c_single_pulse:    cover  property (!reset && !$past(reset) && (out != '0) ##1 (out == '0));

endmodule

bind detect_0_to_1 detect_0_to_1_sva #(.W(32)) u_detect_0_to_1_sva (.*);