// SVA for clock_gating_cell
// Focus: correctness, glitch freedom (with a standard enable protocol), and concise coverage.

module clock_gating_cell_sva (
  input logic clk,
  input logic enable,
  input logic gated_clk
);

  // Environment assumption (typical for glitch-free clock gating):
  // enable may only change while clk is low.
  assume_en_change_only_when_clk_low_pos: assume property (@(posedge enable) !clk);
  assume_en_change_only_when_clk_low_neg: assume property (@(negedge enable) !clk);

  // Combinational equivalence (sanity check at any relevant edge)
  a_and_equivalence: assert property (
    @(posedge clk or negedge clk or posedge enable or negedge enable)
      gated_clk == (clk & enable)
  );

  // No X on output when inputs are known
  a_no_x_out_when_inputs_known: assert property (
    @(posedge clk or negedge clk or posedge enable or negedge enable)
      (!$isunknown({clk,enable})) |-> !$isunknown(gated_clk)
  );

  // Gated clock only rises on a clk rising edge when enabled
  a_rise_only_on_clk_rise: assert property (
    @(posedge clk) enable |-> $rose(gated_clk)
  );

  // Gated clock only falls on a clk falling edge when enabled
  a_fall_only_on_clk_fall: assert property (
    @(negedge clk) enable |-> $fell(gated_clk)
  );

  // When disabled, clk edges must not toggle gated_clk (remains 0)
  a_no_edges_when_disabled_pos: assert property (@(posedge clk) !enable |-> !gated_clk && $stable(gated_clk));
  a_no_edges_when_disabled_neg: assert property (@(negedge clk) !enable |-> !gated_clk && $stable(gated_clk));

  // Enable edges must not directly toggle gated_clk (glitch-free w.r.t. enable)
  a_no_gclk_change_on_enable_edge: assert property (
    @(posedge enable or negedge enable) $stable(gated_clk)
  );

  // Any gated_clk change must be explained by an input change (structural sanity)
  a_gclk_changes_only_if_inputs_change: assert property (
    @(posedge clk or negedge clk or posedge enable or negedge enable)
      $changed(gated_clk) |-> ($changed(clk) || $changed(enable))
  );

  // Minimal functional coverage
  c_gclk_rises:  cover property (@(posedge clk or negedge clk or posedge enable or negedge enable) $rose(gated_clk));
  c_gclk_falls:  cover property (@(posedge clk or negedge clk or posedge enable or negedge enable) $fell(gated_clk));
  c_enable_low_edges: cover property (@(posedge clk) !enable);
  c_enable_high_edges: cover property (@(posedge clk) enable);
  c_enable_rise_clk_low: cover property (@(posedge enable) !clk);
  c_enable_fall_clk_low: cover property (@(negedge enable) !clk);
  // Illegal scenario coverage (would violate assumption; useful in sim to detect bad stimulus)
  c_illegal_enable_rise_clk_high: cover property (@(posedge enable) clk);
  c_illegal_enable_fall_clk_high: cover property (@(negedge enable) clk);

endmodule

// Bind SVA to DUT
bind clock_gating_cell clock_gating_cell_sva sva_i (.*);