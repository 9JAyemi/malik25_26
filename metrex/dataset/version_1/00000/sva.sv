module binary_counter_sva (
  input logic clk,
  input logic [3:0] reset,   // Active when reset == 4'b1111 (synchronous, active-high when all bits = 1)
  input logic [3:0] enable,  // Increment when enable == 4'b1111
  input logic [3:0] count
);
  // Analysis:
  // - Clock: clk (posedge)
  // - Reset: synchronous, active-high when reset == 4'b1111
  // - Logic: sequential (posedge clocked)
  // - Behavior:
  //     * If (reset == 4'b1111) at a clock edge, count is set to 4'b0000.
  //     * Else, if (enable == 4'b1111), count increments by 1, wrapping to 0 when it was 4'b1111.
  //     * Else, count holds its value.

  ///// Reset behavior /////
  // Synchronous reset clears the counter on the next cycle when reset == 4'b1111 at the current cycle.
  check_reset_clears_next: assert property (
    @(posedge clk) (reset == 4'b1111) |=> (count == 4'b0000)
  );

  // If reset was asserted in the previous cycle, the counter must be 0 now.
  check_prev_reset_effect: assert property (
    @(posedge clk) $past(reset == 4'b1111) |-> (count == 4'b0000)
  );

  ///// Hold behavior when not enabled /////
  // If not in reset and enable != 4'b1111, the counter holds its value on the next cycle.
  check_hold_when_not_enabled: assert property (
    @(posedge clk) disable iff (reset == 4'b1111)
      (enable != 4'b1111) |=> (count == $past(count))
  );

  ///// Increment/wrap behavior when fully enabled /////
  // If not in reset and enable == 4'b1111, the next counter value equals previous + 1 (wraps to 0 from 4'hF).
  check_increment_or_wrap_when_enabled: assert property (
    @(posedge clk) disable iff (reset == 4'b1111)
      (enable == 4'b1111) |=> (count == (($past(count) == 4'hF) ? 4'h0 : ($past(count) + 4'd1)))
  );

  ///// Change qualification /////
  // If the counter changed and the previous cycle was not in reset, the previous enable must have been 4'b1111.
  check_change_requires_prev_enable: assert property (
    @(posedge clk) disable iff (reset == 4'b1111)
      ($changed(count) && !$past(reset == 4'b1111)) |-> $past(enable == 4'b1111)
  );

  // Without enable in the previous cycle (and not in reset), a 0xF value must not wrap; it must hold at 0xF.
  check_no_wrap_without_prev_enable: assert property (
    @(posedge clk) disable iff (reset == 4'b1111)
      ($past(reset != 4'b1111) && ($past(count) == 4'hF) && ($past(enable != 4'hF))) |-> (count == 4'hF)
  );

  ///// Equivalent next-state checks using previous-cycle control /////
  // If the previous cycle had enable == 4'b1111 and was not in reset, the counter must have incremented (with wrap).
  check_prev_enable_drives_increment: assert property (
    @(posedge clk) disable iff (reset == 4'b1111)
      ($past(reset != 4'b1111) && $past(enable == 4'b1111))
      |-> (count == (($past(count) == 4'hF) ? 4'h0 : ($past(count) + 4'd1)))
  );

  // If the previous cycle had enable != 4'b1111 and was not in reset, the counter must hold its value.
  check_prev_enable_low_holds: assert property (
    @(posedge clk) disable iff (reset == 4'b1111)
      ($past(reset != 4'b1111) && $past(enable != 4'b1111))
      |-> (count == $past(count))
  );

  ///// Reset precedence /////
  // If both reset and enable are 4'b1111 at a clock edge, reset takes precedence and clears count on the next cycle.
  check_reset_precedence_over_enable: assert property (
    @(posedge clk) (reset == 4'b1111 && enable == 4'b1111) |=> (count == 4'b0000)
  );

  ///// Step-size sanity (no multi-step changes) /////
  // When the previous cycle was not in reset, the counter either holds or advances by exactly one (with wrap).
  check_single_step_progress: assert property (
    @(posedge clk)
      ($past(reset != 4'b1111))
      |-> ( (count == $past(count)) ||
            (count == (($past(count) == 4'hF) ? 4'h0 : ($past(count) + 4'd1))) )
  );

endmodule