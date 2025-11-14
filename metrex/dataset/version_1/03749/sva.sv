// SVA for dff_async_reset (note: reset is synchronous active-low despite module name)
module dff_async_reset_sva (
  input clk,
  input reset, // active-low
  input d,
  input q
);

  default clocking cb @ (posedge clk); endclocking

  bit past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Functional next-state relation (single, strong check)
  // Next q equals: (reset_low ? 0 : d)
  assert property (cb disable iff (!past_valid)
    q == ( $past(reset) ? $past(d) : 1'b0 )
  ) else $error("q next-state mismatch: q=%0b, past(d)=%0b, past(reset)=%0b", q, $past(d), $past(reset));

  // Sanity: reset must not be X at sampling
  assert property (cb !$isunknown(reset))
    else $error("reset is X/Z at clk edge");

  // No-X propagation when inputs are known
  assert property (cb (reset && !$isunknown(d)) |=> !$isunknown(q))
    else $error("q became X/Z despite known reset=1 and d");

  // Coverage: exercise reset assert/deassert and data capture to both 0 and 1
  cover property (cb $fell(reset));      // reset asserted (1->0)
  cover property (cb $rose(reset));      // reset deasserted (0->1)
  cover property (cb (reset &&  d) |=> (q==1)); // capture 1
  cover property (cb (reset && !d) |=> (q==0)); // capture 0
  cover property (cb reset ##1 reset ##1 (q != $past(q))); // observe a q toggle under reset=1

endmodule

// Bind into DUT
bind dff_async_reset dff_async_reset_sva sva_i (.*);