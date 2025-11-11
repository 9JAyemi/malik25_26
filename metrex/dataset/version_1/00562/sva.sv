// SVA for DFF_EN_CLK_GATE
// Bind into the DUT to observe internal gated_clk

module DFF_EN_CLK_GATE_sva (
  input  logic        clk,
  input  logic        en,
  input  logic        te,
  input  logic [31:0] d,
  input  logic [31:0] q,
  input  logic        gated_clk
);

  logic clken;
  assign clken = en & te;

  // Clock-gate correctness (pass-through when enabled, forced low when disabled)
  assert property (@(posedge clk) clken  |-> $rose(gated_clk));
  assert property (@(negedge clk) clken  |-> $fell(gated_clk));
  assert property (@(posedge clk) !clken |-> !gated_clk);
  assert property (@(negedge clk) !clken |-> !gated_clk);

  // No glitches: gated_clk may only toggle when clk toggles and clken is high
  assert property ( $rose(gated_clk) |-> (clken && $rose(clk)) );
  assert property ( $fell(gated_clk) |-> (clken && $fell(clk)) );

  // Gate control must change only when clk is low (safe gating protocol)
  assert property ( $changed(clken) |-> !clk );

  // Flip-flop functional behavior
  assert property (@(posedge gated_clk) 1 |=> q == $past(d,1,gated_clk));
  assert property (@(posedge clk) !clken |-> $stable(q));
  assert property (@(posedge clk) $changed(q) |-> clken);

  // Sanity: no X on key edges
  assert property (@(posedge gated_clk) !$isunknown(d));
  assert property (@(posedge clk or negedge clk) !$isunknown({clk,en,te,gated_clk}));

  // Coverage: see both gated and ungated operation, and data capture
  cover property (@(posedge clk) !clken);
  cover property (@(posedge clk) clken  && $rose(gated_clk));
  cover property (@(posedge clk) !clken ##1 clken ##1 !clken);
  cover property (@(posedge clk) clken && $changed(q));

endmodule

bind DFF_EN_CLK_GATE DFF_EN_CLK_GATE_sva sva (
  .clk       (clk),
  .en        (en),
  .te        (te),
  .d         (d),
  .q         (q),
  .gated_clk (gated_clk)
);