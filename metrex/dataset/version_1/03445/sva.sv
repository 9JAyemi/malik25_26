// SVA for dual_edge_ff
// Focused, high-quality checks + concise coverage
`ifndef SYNTHESIS
module dual_edge_ff_sva (
  input logic clk,
  input logic d,
  input logic q,
  input logic q1,
  input logic q2
);

  // FF1 captures D on posedge
  assert property (@(posedge clk) ##0 (q1 == d))
    else $error("dual_edge_ff: q1 must equal d after posedge");

  // FF2 captures q1 on negedge
  assert property (@(negedge clk) ##0 (q2 == q1))
    else $error("dual_edge_ff: q2 must equal q1 after negedge");

  // End-to-end: at each negedge, q equals D sampled at the preceding posedge
  assert property (@(negedge clk) q == $past(d, 0, posedge clk))
    else $error("dual_edge_ff: q must equal d sampled at prior posedge");

  // q must mirror q2 (combinational assign) at all clock edges
  assert property (@(posedge clk or negedge clk) q == q2)
    else $error("dual_edge_ff: q must equal q2");

  // Minimal functional coverage
  cover property (@(posedge clk) ##0 $changed(q1));                               // FF1 updates
  cover property (@(negedge clk) ##0 $changed(q2));                               // FF2 updates
  cover property (@(negedge clk) $past($rose(d), 0, posedge clk) && $rose(q));    // 0->1 path
  cover property (@(negedge clk) $past($fell(d), 0, posedge clk) && $fell(q));    // 1->0 path

endmodule

bind dual_edge_ff dual_edge_ff_sva u_dual_edge_ff_sva (.*);
`endif