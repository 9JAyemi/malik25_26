// SVA for debounce and clkDiv
// Concise, high-signal-quality checks with essential functional coverage.

`ifndef SYNTHESIS

// -------------------------------
// Assertions bound into debounce
// -------------------------------
module debounce_sva;
  // Inherit DUT scope; signals: clk, but, debounced, debTimer
  localparam int W = 10;
  localparam logic [W-1:0] ALL_ONES = {W{1'b1}};

  default clocking cb @(posedge clk); endclocking

  // debTimer clears whenever output equals input (per RTL)
  ap_timer_resets_when_equal:
    assert property (disable iff ($isunknown({but,debounced,debTimer}))
      (debounced == but) |=> debTimer == '0);

  // While input differs from output and not saturated, timer increments, output holds
  ap_timer_increments_when_diff:
    assert property (disable iff ($isunknown({but,debounced,debTimer}))
      (but != debounced && debTimer != ALL_ONES)
      |=> (debTimer == $past(debTimer,1,'0) + 1) && (debounced == $past(debounced,1,debounced)));

  // Upon saturation with persistent difference, next cycle updates output; timer holds at ALL_ONES that cycle
  ap_update_after_saturation:
    assert property (disable iff ($isunknown({but,debounced,debTimer}))
      (but != debounced && debTimer == ALL_ONES)
      |=> (debounced == $past(but)) && (debTimer == $past(debTimer)));

  // Any output change must be caused by prior saturation with sustained difference
  ap_change_only_after_max:
    assert property (disable iff ($isunknown({but,debounced,debTimer}))
      (debounced != $past(debounced))
      |-> ($past(debTimer) == ALL_ONES && $past(but != $past(debounced))));

  // After an output update, timer clears on the following cycle (due to equality)
  ap_clear_after_update:
    assert property (disable iff ($isunknown({but,debounced,debTimer}))
      (debounced != $past(debounced)) |=> debTimer == '0);

  // Coverage: both output directions, full stable window, and bounce-induced reset
  cp_debounced_rise:  cover property (disable iff ($isunknown({but,debounced,debTimer})) $rose(debounced));
  cp_debounced_fall:  cover property (disable iff ($isunknown({but,debounced,debTimer})) $fell(debounced));
  cp_full_window_then_update:
    cover property (disable iff ($isunknown({but,debounced,debTimer}))
      (but != debounced)[*1024] ##1 (debounced == but));
  cp_bounce_resets_timer:
    cover property (disable iff ($isunknown({but,debounced,debTimer}))
      (but != debounced) ##1 (but == debounced && debTimer == '0));
endmodule

bind debounce debounce_sva d_sva();

// -------------------------------
// Assertions bound into clkDiv
// -------------------------------
module clkDiv_sva;
  // Inherit DUT scope; signals: clk, count, divClk, param n
  localparam int N = n;

  default clocking cb @(posedge clk); endclocking

  // Counter increments by 1 every cycle (modulo 2^N)
  ap_count_increments:
    assert property (disable iff ($isunknown(count))
      1 |=> count == $past(count,1,'0) + 1);

  // Output is the MSB of the counter
  ap_div_matches_msb:
    assert property (disable iff ($isunknown({divClk,count}))
      1 |=> divClk == count[N-1]);

  // Coverage: divider toggles and counter wrap observed
  cp_div_toggle: cover property ($rose(divClk) or $fell(divClk));
  cp_counter_wrap: cover property (count == '0);
endmodule

bind clkDiv clkDiv_sva cd_sva();

`endif