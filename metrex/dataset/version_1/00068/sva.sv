// SVA checker for clock_gate_module
module clock_gate_module_sva (
  input logic CLK,
  input logic EN,
  input logic TE,
  input logic RESET,
  input logic ENCLK
);

  // Asynchronous reset clears output immediately
  a_async_reset_clears: assert property (@(posedge RESET) ENCLK == 1'b0);

  // While RESET is high, ENCLK must be 0 on every posedge CLK
  a_reset_dominates:    assert property (@(posedge CLK) RESET |-> ENCLK == 1'b0);

  // Functional priority and outputs on posedge CLK
  a_te_forces_on:       assert property (@(posedge CLK) disable iff (RESET) TE |-> ENCLK == 1'b1);
  a_en_sets_on:         assert property (@(posedge CLK) disable iff (RESET) (!TE && EN) |-> ENCLK == 1'b1);
  a_both_low_clears:    assert property (@(posedge CLK) disable iff (RESET) (!TE && !EN) |-> ENCLK == 1'b0);

  // TE drop with EN low clears on next posedge
  a_te_drop_clears:     assert property (@(posedge CLK) disable iff (RESET) $fell(TE) && !EN |-> ENCLK == 1'b0);

  // No mid-cycle glitches: ENCLK must not change on negedge CLK
  a_no_glitch_negedge:  assert property (@(negedge CLK) disable iff (RESET) $stable(ENCLK));

  // Known-value check
  a_known_enclk_clk:    assert property (@(posedge CLK)   !$isunknown(ENCLK));
  a_known_enclk_rst:    assert property (@(posedge RESET) !$isunknown(ENCLK));

  // Coverage: exercise key behaviors
  c_te_force:           cover property (@(posedge CLK) disable iff (RESET) $rose(TE) ##1 ENCLK == 1'b1);
  c_en_gate:            cover property (@(posedge CLK) disable iff (RESET) !TE && $rose(EN) ##1 ENCLK == 1'b1);
  c_disable_path:       cover property (@(posedge CLK) disable iff (RESET) !TE && $fell(EN) ##1 ENCLK == 1'b0);
  c_te_override:        cover property (@(posedge CLK) disable iff (RESET) (!EN && $rose(TE)) ##1 ENCLK == 1'b1);
  c_te_drop_disable:    cover property (@(posedge CLK) disable iff (RESET) (!EN && $fell(TE)) ##1 ENCLK == 1'b0);

endmodule

// Bind the checker to all instances of the DUT
bind clock_gate_module clock_gate_module_sva u_clock_gate_module_sva (
  .CLK   (CLK),
  .EN    (EN),
  .TE    (TE),
  .RESET (RESET),
  .ENCLK (ENCLK)
);