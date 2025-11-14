// SVA for freq_divider
module freq_divider_sva #(parameter int unsigned n = 2)
(
  input  logic        clk_in,
  input  logic        clk_out,
  input  logic [31:0] count
);

  default clocking cb @(posedge clk_in); endclocking

  // Parameter sanity
  initial assert (n > 0) else $error("freq_divider: n must be > 0");

  // Start after first clock to safely use $past
  bit started;
  always_ff @(posedge clk_in) started <= 1'b1;

  // No X/Z on key state after first edge
  assert property (disable iff (!started) !$isunknown({clk_out, count}));

  // Count stays within range [0, n-1]
  assert property (disable iff (!started) count < n);

  // If last cycle was wrap (count==n-1), then toggle and reset to 0
  assert property (disable iff (!started)
                   $past(count) == n-1 |-> (clk_out == ~$past(clk_out) && count == 0));

  // If last cycle was not wrap, then increment and hold output
  assert property (disable iff (!started)
                   $past(count) != n-1 |-> (count == $past(count)+1 && clk_out == $past(clk_out)));

  // Any toggle must be caused by wrap
  assert property (disable iff (!started)
                   $changed(clk_out) |-> $past(count) == n-1);

  // Any toggle coincides with count reset to 0
  assert property (disable iff (!started)
                   $changed(clk_out) |-> count == 0);

  // Coverage: observe correct n-cycle spacing between toggles
  cover property (disable iff (!started)
                  $changed(clk_out) |=> !$changed(clk_out) [* (n-1)] ##1 $changed(clk_out));

  // Coverage: see both edges at least once
  cover property (disable iff (!started) $rose(clk_out));
  cover property (disable iff (!started) $fell(clk_out));

endmodule

// Bind into DUT
bind freq_divider freq_divider_sva #(.n(n)) u_freq_divider_sva (.*);