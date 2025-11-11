// SVA for dual_edge_triggered_ff
// Focused, concise checks and coverage of reset and dual-edge transfer

module dual_edge_triggered_ff_sva (
  input clk,
  input reset,
  input data,
  input q,
  input q1,
  input q2
);

  // Reset effects
  property p_posedge_reset_clears;
    @(posedge clk) reset |-> (q1 == 1'b0 && q2 == 1'b0);
  endproperty
  assert property (p_posedge_reset_clears);

  property p_negedge_reset_clears_q;
    @(negedge clk) reset |-> (q == 1'b0);
  endproperty
  assert property (p_negedge_reset_clears_q);

  // Posedge pipeline behavior
  property p_q1_loads_data_on_posedge;
    @(posedge clk) !reset |-> (q1 == $past(data));
  endproperty
  assert property (p_q1_loads_data_on_posedge);

  property p_q2_gets_prev_q1_on_posedge;
    @(posedge clk) !reset |-> (q2 == $past(q1));
  endproperty
  assert property (p_q2_gets_prev_q1_on_posedge);

  // Negedge output transfer from last posedge q2
  property p_q_follows_q2_from_last_posedge;
    @(negedge clk) !reset |-> (q == $past(q2, 1, posedge clk));
  endproperty
  assert property (p_q_follows_q2_from_last_posedge);

  // Cross-edge reset interaction: if reset at last posedge, q must be 0 at this negedge
  property p_q_zero_if_reset_seen_at_last_posedge;
    @(negedge clk) $past(reset, 1, posedge clk) |-> (q == 1'b0);
  endproperty
  assert property (p_q_zero_if_reset_seen_at_last_posedge);

  // End-to-end: with no reset over the two relevant posedges and this negedge,
  // q equals data from the previous posedge (one posedge before the most recent one)
  property p_q_matches_prior_data_when_no_reset;
    @(negedge clk)
      !reset && !$past(reset, 1, posedge clk) && !$past(reset, 2, posedge clk)
      |-> (q == $past(data, 2, posedge clk));
  endproperty
  assert property (p_q_matches_prior_data_when_no_reset);

  // Basic sanity: reset is known on both edges (helps avoid X-driven surprises)
  property p_reset_known_posedge;  @(posedge clk) !$isunknown(reset); endproperty
  property p_reset_known_negedge;  @(negedge clk) !$isunknown(reset); endproperty
  assert property (p_reset_known_posedge);
  assert property (p_reset_known_negedge);

  // Coverage
  cover property (@(posedge clk) reset);
  cover property (@(negedge clk) reset);
  cover property (@(posedge clk) !reset && $changed(data));
  cover property (@(negedge clk) !reset && $changed(q));
  cover property (@(negedge clk) !reset && (q == $past(data, 2, posedge clk)));

endmodule

bind dual_edge_triggered_ff dual_edge_triggered_ff_sva sva_i (.*);