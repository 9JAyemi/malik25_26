// SVA for clock_gate
// Bind this module to each clock_gate instance:
// bind clock_gate clock_gate_sva cg_sva (.*);

module clock_gate_sva (
  input logic CLK,
  input logic EN,
  input logic TE,
  input logic ENCLK,
  input logic gated_clk
);

  // Sanity: two-state at clock edges
  assert property (@(posedge CLK or negedge CLK) !$isunknown({CLK,EN,TE,gated_clk,ENCLK}));

  // Internal gating register must reflect EN & !TE at each posedge
  assert property (@(posedge CLK) gated_clk == (EN && !TE));

  // When enabled (TE or gated_clk), ENCLK must equal CLK at both edges
  assert property (@(posedge CLK)   (TE || gated_clk) |-> ENCLK == 1'b1);
  assert property (@(negedge CLK)   (TE || gated_clk) |-> ENCLK == 1'b0);

  // When disabled, ENCLK must not toggle at the corresponding CLK edge
  assert property (@(posedge CLK)  (!TE && !gated_clk) |-> !$rose(ENCLK));
  assert property (@(negedge CLK)  (!TE && !gated_clk) |-> !$fell(ENCLK));

  // Glitch-free: ENCLK edges only occur with coincident CLK edges and only when enabled
  assert property (@(posedge ENCLK)  $rose(CLK) && (TE || gated_clk));
  assert property (@(negedge ENCLK)  $fell(CLK) && (TE || gated_clk));

  // Coverage: pass-through via TE
  cover property (@(posedge CLK) TE && $rose(ENCLK));
  cover property (@(negedge CLK) TE && $fell(ENCLK));

  // Coverage: functional gating via EN (TE low, gated enabled)
  cover property (@(posedge CLK) (!TE && gated_clk) && $rose(ENCLK));
  cover property (@(negedge CLK) (!TE && gated_clk) && $fell(ENCLK));

  // Coverage: disabled state (no toggles at edges)
  cover property (@(posedge CLK) (!TE && !gated_clk) && !$rose(ENCLK));
  cover property (@(negedge CLK) (!TE && !gated_clk) && !$fell(ENCLK));

  // Coverage: control activity
  cover property (@(posedge CLK) $rose(EN));
  cover property (@(posedge CLK) $fell(EN));
  cover property (@(posedge CLK) $rose(TE));
  cover property (@(posedge CLK) $fell(TE));

endmodule