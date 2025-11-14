// SVA for toggle2pulse: out should pulse when in toggles (XOR with previous in)

module toggle2pulse_sva (input logic clk, reset, in, out);
  default clocking cb @(posedge clk); endclocking

  // Track that $past() is valid
  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Sanity: no X/Z on sampled signals
  a_no_x: assert property (!$isunknown({reset, in, out}));

  // Reset behavior: during reset, out mirrors in
  a_reset_out_eq_in: assert property (reset |-> (out == in));

  // On the cycle reset deasserts, out must be 0 (flop captures in, XOR cancels)
  a_release_zero: assert property (past_valid && $fell(reset) |-> (out == 1'b0));

  // Main functional relation when not near reset edge
  a_xor_run: assert property (past_valid && !reset && !$past(reset) |-> (out == (in ^ $past(in))));

  // Toggle implies a pulse (outside reset edges)
  a_toggle_implies_pulse: assert property (
    past_valid && !reset && !$past(reset) && (in != $past(in)) |-> out
  );

  // No pulse without a toggle (outside reset edges)
  a_no_pulse_without_toggle: assert property (
    past_valid && !reset && !$past(reset) && out |-> (in != $past(in))
  );

  // A single toggle yields a single-cycle pulse if no second toggle next cycle
  a_one_cycle_if_no_second_toggle: assert property (
    past_valid && !reset && !$past(reset) && (in != $past(in))
    |-> ##1 (!reset && !$past(reset) && (in == $past(in)) && !out)
  );

  // Coverage
  c_rise_toggle:  cover property (past_valid && !reset && !$past(reset) && $rose(in) && out);
  c_fall_toggle:  cover property (past_valid && !reset && !$past(reset) && $fell(in) && out);
  c_back_to_back: cover property (past_valid && !reset && !$past(reset) && out ##1 out ##1 out);
  c_reset_release: cover property (past_valid && $fell(reset) && (out == 1'b0));
  c_reset_high_1: cover property (reset && in && out);
  c_reset_high_0: cover property (reset && !in && !out);

endmodule

bind toggle2pulse toggle2pulse_sva sva_i (.clk(clk), .reset(reset), .in(in), .out(out));