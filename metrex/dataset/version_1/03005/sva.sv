// SVA for dual_edge_triggered_ff
// Bind into the DUT to check key functionality concisely

module dual_edge_triggered_ff_sva;

  // Functional: q equals d sampled at the previous posedge (half-cycle latency)
  assert property (@(negedge clk) q == $past(d, 1, posedge clk));

  // Staging: q1 holds the sampled d until the negedge
  assert property (@(negedge clk) q1 == $past(d, 1, posedge clk));

  // Structural/stability: q/q2 only update on negedge
  assert property (@(posedge clk) $stable(q) && $stable(q2));

  // Structural/stability: q1 does not update on negedge
  assert property (@(negedge clk) $stable(q1));

  // Continuous-assign correctness: q mirrors q2
  assert property (@(posedge clk or negedge clk) q === q2);

  // Coverage: exercise input/output activity and both value transfers
  cover property (@(posedge clk) d != $past(d));
  cover property (@(negedge clk) q != $past(q));
  cover property (@(negedge clk) $past(d,1,posedge clk) == 1'b0 && q == 1'b0);
  cover property (@(negedge clk) $past(d,1,posedge clk) == 1'b1 && q == 1'b1);

endmodule

bind dual_edge_triggered_ff dual_edge_triggered_ff_sva sva();