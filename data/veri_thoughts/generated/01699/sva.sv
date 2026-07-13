module binary_counter_sva (
  input logic clk,
  input logic reset,   // active-high synchronous reset
  input logic enable,
  input logic [3:0] count
);

  ///// Reset behavior /////
  // After a cycle with reset asserted, count is 0 on the next cycle.
  check_reset_clears_next: assert property (
    @(posedge clk) $past(reset) |-> (count == 4'd0)
  );

  // While reset remains asserted across cycles, count stays 0.
  check_reset_holds_zero: assert property (
    @(posedge clk) reset && $past(reset) |-> (count == 4'd0)
  );

  ///// Enable/hold behavior /////
  // If the previous cycle was not reset and enable was 0, count holds its value.
  check_hold_when_disabled_prev: assert property (
    @(posedge clk) disable iff (reset) $past(!enable && !reset) |-> (count == $past(count))
  );

  // If the previous cycle had enable=1 and no reset, count increments by 1 modulo 16.
  check_increment_when_enabled_prev: assert property (
    @(posedge clk) disable iff (reset) $past(enable && !reset) |-> (count == (($past(count) + 4'd1) & 4'hF))
  );

  // If previous cycle had enable=1 and count was 15, count wraps to 0.
  check_wraparound_on_max: assert property (
    @(posedge clk) disable iff (reset) ($past(enable && !reset) && ($past(count) == 4'hF)) |-> (count == 4'h0)
  );

  // A change in count must be caused by either previous reset or previous enable.
  check_change_requires_prev_enable_or_reset: assert property (
    @(posedge clk) disable iff (reset) $changed(count) |-> ($past(reset) || $past(enable && !reset))
  );

  // If the previous cycle had enable=1 and no reset, count must change.
  check_must_change_when_prev_enable: assert property (
    @(posedge clk) disable iff (reset) $past(enable && !reset) |-> (count != $past(count))
  );

  // With enable=0 in the current cycle (and not in reset), next cycle holds the same value.
  check_hold_when_disabled_curr_to_next: assert property (
    @(posedge clk) disable iff (reset) !enable |-> ##1 (count == $past(count))
  );

endmodule