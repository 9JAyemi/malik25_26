// SVA for dual_edge_triggered_ff and top_module
// Focus: functional latency mapping across edges, with concise, high-quality checks.
// Uses event-argument form of $past(expr, n, event) and guards for history maturity.

////////////////////////////////////////////////////////////
// Assertions for the leaf DUT: dual_edge_triggered_ff
////////////////////////////////////////////////////////////
module sva_dual_edge_triggered_ff (
  input clk,
  input d,
  input q
);
  // Check at each negedge that q equals d sampled two prior posedges
  // Guard against insufficient history and Xs
  default clocking cbn @ (negedge clk); endclocking

  property p_q_maps_to_d_2pos;
    (!$isunknown(q) && !$isunknown($past(d,2, posedge clk)))
      |-> (q === $past(d,2, posedge clk));
  endproperty
  assert property (p_q_maps_to_d_2pos)
    else $error("dual_edge_triggered_ff: q != d delayed by 2 posedges");

  // Basic coverage: q changes and mapping is observed
  cover property ($changed(q));
  cover property (q === $past(d,2, posedge clk));
endmodule

bind dual_edge_triggered_ff sva_dual_edge_triggered_ff
  (.clk(clk), .d(d), .q(q));

////////////////////////////////////////////////////////////
// Assertions for the top-level composition
////////////////////////////////////////////////////////////
module sva_top_module (
  input clk,
  input d,
  input q,
  input q_ff
);
  default clocking cbn @ (negedge clk); endclocking

  // Instance ff1: q_ff equals d delayed by 2 posedges
  property p_ff1_map_2pos;
    (!$isunknown(q_ff) && !$isunknown($past(d,2, posedge clk)))
      |-> (q_ff === $past(d,2, posedge clk));
  endproperty
  assert property (p_ff1_map_2pos)
    else $error("top_module: ff1 q != d delayed by 2 posedges");

  // Instance ff2: q equals q_ff delayed by 2 posedges
  property p_ff2_map_2pos_from_qff;
    (!$isunknown(q) && !$isunknown($past(q_ff,2, posedge clk)))
      |-> (q === $past(q_ff,2, posedge clk));
  endproperty
  assert property (p_ff2_map_2pos_from_qff)
    else $error("top_module: ff2 q != q_ff delayed by 2 posedges");

  // End-to-end composition: q equals d delayed by 5 posedges
  property p_top_end_to_end_5pos;
    (!$isunknown(q) && !$isunknown($past(d,5, posedge clk)))
      |-> (q === $past(d,5, posedge clk));
  endproperty
  assert property (p_top_end_to_end_5pos)
    else $error("top_module: q != d delayed by 5 posedges");

  // Coverage: observe activity and mappings
  cover property ($changed(q_ff));
  cover property ($changed(q));
  cover property (q_ff === $past(d,2, posedge clk));
  cover property (q === $past(q_ff,2, posedge clk));
  cover property (q === $past(d,5, posedge clk));
endmodule

bind top_module sva_top_module
  (.clk(clk), .d(d), .q(q), .q_ff(q_ff));