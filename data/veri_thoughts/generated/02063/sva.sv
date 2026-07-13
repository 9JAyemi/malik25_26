module binary_counter_sva (
  input logic        clock,
  input logic        reset,
  input logic [3:0]  count
);

  // Synchronous reset drives count to 0 on the clock edge.
  check_reset_clears_count: assert property (
    @(posedge clock) reset |-> (count == 4'd0)
  );

  // When not in reset, count increments by 1 each cycle (mod 16).
  check_increment_when_not_reset: assert property (
    @(posedge clock) disable iff (reset || $initstate) count == $past(count) + 4'd1
  );

  // If previous count was 4'hF and not in reset, wrap to 0.
  check_wrap_from_max: assert property (
    @(posedge clock) disable iff (reset || $initstate) ($past(count) == 4'hF) |-> (count == 4'h0)
  );

  // If not in reset and count is 0, previous must have been 4'hF.
  check_zero_implies_prev_max: assert property (
    @(posedge clock) disable iff (reset || $initstate) (count == 4'h0) |-> ($past(count) == 4'hF)
  );

  // First non-reset cycle after reset deassertion produces count==1.
  check_one_after_reset_release: assert property (
    @(posedge clock) disable iff ($initstate) ($past(reset) && !reset) |-> (count == 4'd1)
  );

  // While reset is held, count stays at 0 and is stable.
  check_hold_reset_stable_zero: assert property (
    @(posedge clock) disable iff ($initstate) (reset && $past(reset)) |-> (count == 4'd0 && $stable(count))
  );

  // When not wrapping (prev != 4'hF) and not in reset, the value increases.
  check_monotonic_increase_no_wrap: assert property (
    @(posedge clock) disable iff (reset || $initstate) ($past(count) != 4'hF) |-> (count > $past(count))
  );

  // LSB toggles every cycle when not in reset.
  check_lsb_toggles: assert property (
    @(posedge clock) disable iff (reset || $initstate) (count[0] != $past(count[0]))
  );

  // If previous LSB was 0, bit1 remains the same when not in reset.
  check_bit1_stable_when_prev_lsb0: assert property (
    @(posedge clock) disable iff (reset || $initstate) (!$past(count[0])) |-> (count[1] == $past(count[1]))
  );

  // If previous LSB was 1, bit1 toggles when not in reset.
  check_bit1_toggles_when_prev_lsb1: assert property (
    @(posedge clock) disable iff (reset || $initstate) ($past(count[0])) |-> (count[1] != $past(count[1]))
  );

endmodule