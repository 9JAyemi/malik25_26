module four_bit_register_sva (
  input logic CLK,
  input logic RST,
  input logic [3:0] D,
  input logic [3:0] Q
);

  ///// Reset behavior /////
  // While reset is held low across cycles, Q is 0.
  check_reset_holds_zero: assert property (
    @(posedge CLK) (!RST && $past(!RST)) |-> (Q == 4'b0)
  );

  // If reset is low this cycle, Q is 0 next cycle.
  check_reset_next_cycle_zero: assert property (
    @(posedge CLK) (!RST) |=> (Q == 4'b0)
  );

  // On reset deassertion edge, Q remains 0 in the current cycle.
  check_zero_on_reset_release_cycle: assert property (
    @(posedge CLK) $rose(RST) |-> (Q == 4'b0)
  );

  ///// Functional behavior /////
  // With reset deasserted, Q updates to D with one-cycle latency.
  check_q_follows_d_one_cycle: assert property (
    @(posedge CLK) disable iff (!RST) 1'b1 |=> (Q == $past(D))
  );

  // When not in reset, any change in Q matches the previous D.
  check_q_change_matches_prev_d: assert property (
    @(posedge CLK) disable iff (!RST) $changed(Q) |-> (Q == $past(D))
  );

  // When not in reset for two cycles and D changes, Q changes next cycle.
  check_d_change_propagates: assert property (
    @(posedge CLK) (RST && $past(RST) && (D != $past(D))) |=> (Q != $past(Q))
  );

  // When not in reset for two cycles and D is stable, Q is stable next cycle.
  check_d_stable_keeps_q_stable: assert property (
    @(posedge CLK) (RST && $past(RST) && $stable(D)) |=> (Q == $past(Q))
  );

endmodule