// SVA checker for dual_edge_ff
module dual_edge_ff_sva (
  input logic clk,
  input logic d,
  input logic q,
  input logic q1,
  input logic q2
);

  // Track that we've seen at least one posedge for $past() validity
  logic pos_seen;
  initial pos_seen = 0;
  always @(posedge clk) pos_seen <= 1;

  // Edge-local correctness (post-NBA) on each updating edge
  // q1 captures d at posedge
  assert property (@(posedge clk) ##0 (q1 === d))
    else $error("q1 must equal d after posedge NBA");

  // q2 captures q1 at negedge
  assert property (@(negedge clk) ##0 (q2 === q1))
    else $error("q2 must equal q1 after negedge NBA");

  // q captures q2 at posedge
  assert property (@(posedge clk) ##0 (q === q2))
    else $error("q must equal q2 after posedge NBA");

  // End-to-end behavior: one-posedge latency from d to q
  assert property (@(posedge clk) pos_seen |-> (q === $past(d)))
    else $error("q must equal d from previous posedge");

  // No spurious toggles: if d holds across posedges, q holds as well
  assert property (@(posedge clk) pos_seen && (d === $past(d)) |-> (q === $past(q)))
    else $error("q changed despite stable d across posedges");

  // Coverage: demonstrate both polarities propagate through to q in one posedge
  cover property (@(posedge clk) pos_seen && $rose(d) ##1 $rose(q));
  cover property (@(posedge clk) pos_seen && $fell(d) ##1 $fell(q));

  // Coverage: internal stage activity on their intended edges
  cover property (@(posedge clk) $changed(q1));
  cover property (@(negedge clk) $changed(q2));

endmodule

// Bind the checker to the DUT to observe internals q1/q2
bind dual_edge_ff dual_edge_ff_sva u_dual_edge_ff_sva (
  .clk(clk),
  .d(d),
  .q(q),
  .q1(q1),
  .q2(q2)
);