module d_ff_sva (
  input logic D,
  input logic CLK,
  input logic RESET,
  input logic Q
);

  ///// Asynchronous reset behavior /////
  // When RESET rises, Q must be 0 by the next clock.
  reset_drive_zero_after_rise: assert property (
    @(posedge CLK) $rose(RESET) |=> (Q == 1'b0)
  );

  // While RESET is held across consecutive clocks, Q must be 0.
  reset_hold_zero_when_held: assert property (
    @(posedge CLK) (RESET && $past(RESET)) |-> (Q == 1'b0)
  );

  // On the clock when RESET just fell, Q is still 0 (before new capture).
  reset_deassert_zero_this_cycle: assert property (
    @(posedge CLK) $fell(RESET) |-> (Q == 1'b0)
  );

  ///// Normal capture behavior (not in reset) /////
  // When not in reset for two consecutive clocks, Q equals prior-cycle D.
  capture_q_equals_prev_d: assert property (
    @(posedge CLK) disable iff (RESET) (!$past(RESET)) |-> (Q == $past(D))
  );

  // If D changed in the last cycle (two-cycle history) with no reset, Q changes now.
  q_changes_follow_prev_d_change: assert property (
    @(posedge CLK) disable iff (RESET)
      (!$past(RESET) && !$past(RESET,2) && ($past(D) != $past(D,2))) |-> ($changed(Q))
  );

  // If D was stable over the last cycle (two-cycle history) with no reset, Q is stable now.
  q_stable_when_prev_d_stable: assert property (
    @(posedge CLK) disable iff (RESET)
      (!$past(RESET) && !$past(RESET,2) && ($past(D) == $past(D,2))) |-> (!$changed(Q))
  );

endmodule