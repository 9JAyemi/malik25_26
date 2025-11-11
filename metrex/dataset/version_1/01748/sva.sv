// SVA for dual_edge_triggered_ff
module dual_edge_triggered_ff_sva (
  input clk,
  input d,
  input q,
  input q1
);
  bit pos_seen, neg_seen;
  always @(posedge clk) pos_seen <= 1'b1;
  always @(negedge clk) neg_seen <= 1'b1;

  // q equals d sampled at previous posedge
  assert property (@(posedge clk) pos_seen |-> q === $past(d,1, posedge clk));

  // q1 captures d on posedge (checked at negedge to avoid NBA race)
  assert property (@(negedge clk) pos_seen |-> q1 === $past(d,1, posedge clk));

  // q takes q1 at the previous negedge
  assert property (@(posedge clk) neg_seen |-> q === $past(q1,1, negedge clk));

  // If d was known at previous posedge, q must be known now
  assert property (@(posedge clk) pos_seen && !$isunknown($past(d,1, posedge clk)) |-> !$isunknown(q));

  // Coverage: both transitions of d propagate to q by next posedge
  cover property (@(posedge clk) pos_seen && $rose(d) ##1 q == $past(d,1, posedge clk));
  cover property (@(posedge clk) pos_seen && $fell(d) ##1 q == $past(d,1, posedge clk));
endmodule

bind dual_edge_triggered_ff dual_edge_triggered_ff_sva sva_i (
  .clk(clk),
  .d(d),
  .q(q),
  .q1(q1)
);