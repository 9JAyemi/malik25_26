// SVA checker for clk_gated_module
// Focus: correctness of register capture, gating function, edge alignment, glitch/X checks, and concise coverage.

module clk_gated_module_sva(
  input logic src_clk,
  input logic clk_en,
  input logic gated_clk,
  input logic clk_en_reg
);

  // Track when $past is valid
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge src_clk) past_valid <= 1'b1;

  // Convenience: disable assertions on unknowns or before first valid past
  function automatic logic noX_all;
    noX_all = !$isunknown({src_clk, clk_en, clk_en_reg, gated_clk});
  endfunction

  default clocking cb @(posedge src_clk); endclocking
  clocking cbn @(negedge src_clk); endclocking

  // 1) Registered enable correctness: clk_en_reg captures clk_en on posedge src_clk
  a_reg_capture: assert property (cb
    disable iff (!past_valid || !noX_all())
      clk_en_reg == $past(clk_en)
  );

  // 2) Combinational gating relationship (sanity check)
  a_gate_equation_pos: assert property (cb
    disable iff (!noX_all())
      gated_clk == (src_clk & clk_en_reg)
  );
  a_gate_equation_neg: assert property (cbn
    disable iff (!noX_all())
      gated_clk == (src_clk & clk_en_reg)
  );

  // 3) When disabled, gated clock must be low
  a_en0_forces_low_pos: assert property (cb
    disable iff (!noX_all())
      !clk_en_reg |-> !gated_clk
  );
  a_en0_forces_low_neg: assert property (cbn
    disable iff (!noX_all())
      !clk_en_reg |-> !gated_clk
  );

  // 4) When enabled, gated clock tracks src_clk at both edges
  a_en1_tracks_pos: assert property (cb
    disable iff (!noX_all())
      clk_en_reg |-> (gated_clk == 1'b1) // src_clk is 1 at posedge
  );
  a_en1_tracks_neg: assert property (cbn
    disable iff (!noX_all())
      clk_en_reg |-> (gated_clk == 1'b0) // src_clk is 0 at negedge
  );

  // 5) Rising edges of gated_clk only occur on src_clk rising edge and when enabled
  a_rise_origin: assert property (@(posedge gated_clk)
    !$isunknown({src_clk, clk_en_reg}) |-> ($rose(src_clk) && clk_en_reg)
  );

  // 6) Falling edges of gated_clk only occur on src_clk falling edge,
  //    or immediately at src_clk rising edge when enable deasserts that cycle
  a_fall_origin: assert property (@(negedge gated_clk)
    !$isunknown({src_clk, clk_en_reg}) |->
      ($fell(src_clk) || ($rose(src_clk) && !clk_en_reg))
  );

  // 7) No-X propagation: if inputs to gate are known, output is known
  a_no_x_out: assert property (cb
    (!$isunknown({src_clk, clk_en_reg})) |-> !$isunknown(gated_clk)
  );

  // 8) clk_en_reg only changes on posedge src_clk
  a_reg_changes_only_on_posedge: assert property (
    $changed(clk_en_reg) |-> $rose(src_clk)
  );

  // Coverage
  // C1: See both gated clock edges
  c_gclk_rise:  cover property (@(posedge gated_clk) 1);
  c_gclk_fall:  cover property (@(negedge gated_clk) 1);

  // C2: See enable 0->1 leading to a gated pulse
  c_enable_then_pulse: cover property (cb
    $rose(clk_en) ##1 clk_en_reg && gated_clk
  );

  // C3: See disable at posedge causing immediate or next-edge drop
  c_disable_effect: cover property (cb
    $past(clk_en_reg) && !clk_en_reg
    ##0 ($fell(gated_clk) or ##1 !gated_clk)
  );

endmodule

// Bind the checker to the DUT (includes internal clk_en_reg)
bind clk_gated_module clk_gated_module_sva u_clk_gated_module_sva (
  .src_clk(src_clk),
  .clk_en(clk_en),
  .gated_clk(gated_clk),
  .clk_en_reg(clk_en_reg)
);