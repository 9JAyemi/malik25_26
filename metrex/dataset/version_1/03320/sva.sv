// SystemVerilog Assertions for chatgpt_generate_edge_detect
// Bind these to the DUT (see bind statement at bottom)

module chatgpt_generate_edge_detect_sva (chatgpt_generate_edge_detect dut);

  default clocking cb @(posedge dut.clk); endclocking
  default disable iff (!dut.rst_n);

  // Basic sanity
  ap_no_both:       assert property (!(dut.rise && dut.down));
  ap_rise_1cy:      assert property (dut.rise |=> !dut.rise);
  ap_down_1cy:      assert property (dut.down |=> !dut.down);

  // Golden functional spec: pulses exactly on edges of a
  ap_rise_only_on_rose: assert property (dut.rise |->  $rose(dut.a));
  ap_rise_on_every_rose:assert property ($rose(dut.a) |-> dut.rise);
  ap_down_only_on_fell: assert property (dut.down |->  $fell(dut.a));
  ap_down_on_every_fell:assert property ($fell(dut.a) |-> dut.down);

  // State/output consistency
  ap_idle_outputs:  assert property ((dut.current_state == dut.IDLE)         |-> (!dut.rise && !dut.down));
  ap_rise_outputs:  assert property ((dut.current_state == dut.RISING_EDGE)  |-> ( dut.rise && !dut.down));
  ap_fall_outputs:  assert property ((dut.current_state == dut.FALLING_EDGE) |-> (!dut.rise &&  dut.down));

  // State encoding legality
  ap_state_legal:   assert property (dut.current_state inside {dut.IDLE, dut.RISING_EDGE, dut.FALLING_EDGE});

  // State transitions
  ap_edge_to_idle_r: assert property ((dut.current_state == dut.RISING_EDGE)  |=> (dut.current_state == dut.IDLE));
  ap_edge_to_idle_f: assert property ((dut.current_state == dut.FALLING_EDGE) |=> (dut.current_state == dut.IDLE));
  ap_idle_on_rose:   assert property ((dut.current_state == dut.IDLE && $rose(dut.a)) |=> (dut.current_state == dut.RISING_EDGE));
  ap_idle_on_fell:   assert property ((dut.current_state == dut.IDLE && $fell(dut.a)) |=> (dut.current_state == dut.FALLING_EDGE));

  // Reset behavior and X-checks (not disabled during reset)
  ap_reset_clamps:  assert property (@(posedge dut.clk) !dut.rst_n |-> (dut.current_state == dut.IDLE && !dut.rise && !dut.down));
  ap_no_x_after_rst:assert property (@(posedge dut.clk) dut.rst_n  |-> (!$isunknown({dut.current_state,dut.rise,dut.down})));

  // Coverage
  cp_rise_pulse:    cover property ($rose(dut.a) ##1 dut.rise);
  cp_fall_pulse:    cover property ($fell(dut.a) ##1 dut.down);
  cp_alt_edges:     cover property ($rose(dut.a) ##1 $fell(dut.a) ##1 $rose(dut.a));
  cp_states_r:      cover property (dut.current_state == dut.RISING_EDGE);
  cp_states_f:      cover property (dut.current_state == dut.FALLING_EDGE);

endmodule

// Bind into all instances of the DUT
bind chatgpt_generate_edge_detect chatgpt_generate_edge_detect_sva sva(.dut);