// SVA for dffsi_9
module dffsi_9_sva (
    input  logic        clk,
    input  logic        reset,      // active-low synchronous reset
    input  logic [8:0]  init,
    input  logic [8:0]  d,
    input  logic [8:0]  q
);
  default clocking cb @(posedge clk); endclocking

  // Functional correctness: q equals the previously-selected input (1-cycle latency)
  a_func: assert property (1'b1 |=> (q == $past(reset ? d : init)))
    else $error("dffsi_9: q mismatch against selected source (prev cycle)");

  // Reset must be known at every clock
  a_rst_known: assert property (!$isunknown(reset))
    else $error("dffsi_9: reset is X/Z at posedge clk");

  // Knownness propagation: when the driving source is known, q becomes known next cycle
  a_kn_from_init: assert property ((!reset && !$isunknown(init)) |=> !$isunknown(q))
    else $error("dffsi_9: q X/Z after init-driven cycle");
  a_kn_from_d:    assert property (( reset && !$isunknown(d))   |=> !$isunknown(q))
    else $error("dffsi_9: q X/Z after d-driven cycle");

  // Minimal functional coverage
  c_init_path:  cover property (!reset ##1 (q == $past(init)));
  c_d_path:     cover property ( reset ##1 (q == $past(d)));
  c_rst_fall:   cover property ($fell(reset));
  c_rst_rise:   cover property ($rose(reset));
  c_q_changes:  cover property ($changed(q));
endmodule

bind dffsi_9 dffsi_9_sva sva_dffsi_9 (
  .clk   (clk),
  .reset (reset),
  .init  (init),
  .d     (d),
  .q     (q)
);