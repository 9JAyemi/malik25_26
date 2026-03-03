// SVA for sync_counter. Bind this module to the DUT.
// Focused, high-quality checks + essential coverage.

module sync_counter_sva(
  input logic        clk,
  input logic        reset_n,
  input logic        enable,
  input logic [3:0]  count
);

  // Default clocking for concise properties
  default clocking cb @(posedge clk); endclocking
  default disable iff (!reset_n);

  // ------------------------
  // Asynchronous reset checks (not disabled by reset)
  // ------------------------
  // Immediately force zero on async reset assert
  assert property (disable iff (1'b0) @(negedge reset_n) count == 4'h0)
    else $error("count not 0 on async reset assert");

  // While reset is low, count must stay zero (sampled on clk to keep it simple)
  assert property (disable iff (1'b0) @(posedge clk) !reset_n |-> count == 4'h0)
    else $error("count not 0 while reset_n is low");

  // ------------------------
  // Functional behavior (synchronous)
  // Guard with $past(reset_n) to avoid 1st-cycle-after-reset ambiguity
  // ------------------------
  // Hold when enable==0
  assert property ($past(reset_n) && !enable |=> count == $past(count))
    else $error("count changed while enable==0");

  // Increment by 1 when enable==1 (mod-16 via 4-bit width)
  assert property ($past(reset_n) && enable |=> count == $past(count)+1)
    else $error("count did not increment when enable==1");

  // Explicit wrap check: F -> 0 when enabled
  assert property ($past(reset_n) && enable && count==4'hF |=> count==4'h0)
    else $error("count failed to wrap from F to 0");

  // If out of reset on consecutive cycles, any change must be due to enable
  assert property ((reset_n && $past(reset_n)) |-> (!$changed(count) || $past(enable)))
    else $error("count changed without enable");

  // No X/Z on key signals out of reset
  assert property (!$isunknown({enable, count}))
    else $error("X/Z detected on enable or count");

  // ------------------------
  // Coverage
  // ------------------------
  // See an increment
  cover property ($past(reset_n) && enable |=> count == $past(count)+1);

  // See a hold
  cover property ($past(reset_n) && !enable |=> count == $past(count));

  // See a wrap from F to 0
  cover property ($past(reset_n) && enable && count==4'hF ##1 count==4'h0);

  // Async reset asserted while count was non-zero
  cover property ($fell(reset_n) && $past(count)!=4'h0);

endmodule

// Bind into the DUT
bind sync_counter sync_counter_sva sva_i (
  .clk     (clk),
  .reset_n (reset_n),
  .enable  (enable),
  .count   (count)
);