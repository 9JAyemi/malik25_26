// SVA for c_clkgate: concise, high-quality checks and coverage

module c_clkgate_sva (input logic clk, enable, clk_gated, enable_q);

  // 1) Functional equivalence: clk_gated == clk & enable_q (when known)
  assert property (@(posedge clk or negedge clk or posedge enable_q or negedge enable_q)
                   (!$isunknown({clk, enable_q, clk_gated})) |-> (clk_gated == (clk & enable_q)))
    else $error("clk_gated must equal clk & enable_q");

  // 2) Latch discipline: enable_q must never change while clk is high
  assert property (@(posedge clk or negedge clk or posedge enable_q or negedge enable_q)
                   !(clk && $changed(enable_q)))
    else $error("enable_q changed while clk was high");

  // 3) Edge alignment and levels
  assert property (@(posedge clk) (!$isunknown(enable_q)) |-> (clk_gated == enable_q))
    else $error("At posedge clk, clk_gated must equal enable_q");
  assert property (@(negedge clk) (clk_gated == 1'b0))
    else $error("At negedge clk, clk_gated must be 0");

  assert property (@(posedge clk) (!$isunknown(enable_q)) |-> ($rose(clk_gated) == enable_q))
    else $error("Rising edge of clk_gated must match enable_q at posedge clk");
  assert property (@(negedge clk) (!$isunknown(enable_q)) |-> ($fell(clk_gated) == enable_q))
    else $error("Falling edge of clk_gated must match enable_q at negedge clk");

  // 4) No glitches: clk_gated only changes on clk edges
  assert property (@(posedge clk or negedge clk or posedge clk_gated or negedge clk_gated)
                   (!$isunknown({clk, clk_gated, $past(clk_gated)})) && $changed(clk_gated)
                   |-> $changed(clk))
    else $error("clk_gated changed without a clk edge");

  // 5) Latch transparency when clk is low: enable_q tracks enable (next delta)
  assert property (@(posedge enable or negedge enable or posedge clk or negedge clk)
                   (!clk && $changed(enable)) |=> (enable_q == enable))
    else $error("enable_q did not track enable while clk was low");

  // Coverage: open gate pulse, held closed, and enable toggling in low phase
  cover property (@(posedge clk) enable_q && $rose(clk_gated));
  cover property (@(posedge clk) !enable_q && !clk_gated);
  cover property (@(posedge enable or negedge enable) !clk);

endmodule

bind c_clkgate c_clkgate_sva u_c_clkgate_sva(.clk(clk), .enable(enable),
                                             .clk_gated(clk_gated), .enable_q(enable_q));