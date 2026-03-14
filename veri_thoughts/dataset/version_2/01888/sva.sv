module up_down_counter_sva (
  input logic clk,
  input logic reset,      // active-high async reset
  input logic up_down,    // 1=up, 0=down
  input logic [2:0] count
);

  ///// Reset behavior /////
  // When reset is asserted at a clock edge, count must be 0.
  reset_forces_zero: assert property (
    @(posedge clk) reset |-> (count == 3'd0)
  );

  // While reset stays asserted across cycles, count remains 0.
  reset_holds_zero: assert property (
    @(posedge clk) ($past(reset) && reset) |-> (count == 3'd0)
  );

  ///// State update rules /////
  // On the cycle after reset deasserts, next count is based on current up_down from 0.
  post_reset_first_update: assert property (
    @(posedge clk) disable iff (reset)
      ($past(reset) && !reset) |-> (count == (up_down ? 3'd1 : 3'd7))
  );

  // If previous cycle was up mode and not at 7, increment by 1.
  count_up_increment: assert property (
    @(posedge clk) disable iff (reset)
      ($past(!reset) && $past(up_down) && ($past(count) != 3'd7)) |-> (count == ($past(count) + 3'd1))
  );

  // If previous cycle was up mode at 7, wrap to 0.
  count_up_wrap: assert property (
    @(posedge clk) disable iff (reset)
      ($past(!reset) && $past(up_down) && ($past(count) == 3'd7)) |-> (count == 3'd0)
  );

  // If previous cycle was down mode and not at 0, decrement by 1.
  count_down_decrement: assert property (
    @(posedge clk) disable iff (reset)
      ($past(!reset) && !$past(up_down) && ($past(count) != 3'd0)) |-> (count == ($past(count) - 3'd1))
  );

  // If previous cycle was down mode at 0, wrap to 7.
  count_down_wrap: assert property (
    @(posedge clk) disable iff (reset)
      ($past(!reset) && !$past(up_down) && ($past(count) == 3'd0)) |-> (count == 3'd7)
  );

  ///// General invariants derived from the update rules /////
  // Out of reset, count must change every cycle (either +1 or -1 mod 8).
  count_changes_every_cycle: assert property (
    @(posedge clk) disable iff (reset)
      $past(!reset) |-> (count != $past(count))
  );

  // Out of reset, the step size is exactly +/-1 modulo 8.
  one_step_only: assert property (
    @(posedge clk) disable iff (reset)
      $past(!reset) |-> ((count == ($past(count) + 3'd1)) || (count == ($past(count) - 3'd1)))
  );

  // Out of reset, LSB toggles every cycle due to +/-1 update.
  lsb_toggles: assert property (
    @(posedge clk) disable iff (reset)
      $past(!reset) |-> (count[0] != $past(count[0]))
  );

endmodule