module d_flip_flop_as_sva (
  input logic clk,
  input logic as,
  input logic [7:0] d,
  input logic [7:0] q
);
  // Clock: clk (posedge). No explicit reset. q updates to d when as==0; holds when as==1.

  // When as is LOW, q captures d on the next clock.
  check_load_on_as_low: assert property (
    @(posedge clk) (~as) |=> (q == $past(d))
  );

  // When as is HIGH, q holds its previous value on the next clock.
  check_hold_when_as_high: assert property (
    @(posedge clk) (as) |=> (q == $past(q))
  );

  // If q changed since the last clock, then as was LOW in the previous cycle.
  check_q_change_requires_prev_enable: assert property (
    @(posedge clk) $changed(q) |-> $past(~as)
  );

  // If q changed since the last clock, the new q equals last cycle's d.
  check_q_change_matches_prev_d: assert property (
    @(posedge clk) $changed(q) |-> (q == $past(d))
  );

  // Exact next-state function for q based on previous cycle's as, d, and q.
  check_next_state_function: assert property (
    @(posedge clk) q == ($past(~as) ? $past(d) : $past(q))
  );

  // If as is LOW and d differs from current q, q must change next cycle.
  check_update_changes_when_data_diff: assert property (
    @(posedge clk) (~as && (d != q)) |=> (q != $past(q))
  );

  // If as is LOW and d equals current q, q must not change next cycle.
  check_update_no_change_when_data_same: assert property (
    @(posedge clk) (~as && (d == q)) |=> (q == $past(q))
  );

  // While holding (as HIGH), changes on d do not affect q.
  check_data_changes_do_not_affect_when_as_high: assert property (
    @(posedge clk) (as && $changed(d)) |=> (q == $past(q))
  );

  // On a falling edge of as, q captures d on the next clock.
  check_fall_as_triggers_update: assert property (
    @(posedge clk) $fell(as) |=> (q == $past(d))
  );

  // On a rising edge of as, q must hold on the next clock.
  check_rise_as_holds_value: assert property (
    @(posedge clk) $rose(as) |=> (q == $past(q))
  );

endmodule