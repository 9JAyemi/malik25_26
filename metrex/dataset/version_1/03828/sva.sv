// SVA for freq_syn
bind freq_syn freq_syn_sva();

module freq_syn_sva;

  default clocking cb @(posedge clk_ref); endclocking

  bit started;
  initial started = 1'b0;
  always @(posedge clk_ref) started <= 1'b1;

  default disable iff (!started);

  // Core functional checks
  a_ctrl_capture:        assert property (ctrl_reg == $past(ctrl));
  a_phase_inc_func:      assert property (phase_inc == (ctrl_reg * (33'h1_0000_0000 - phase_ref)) / (2**n));
  a_phase_accum_update:  assert property (phase_accum == 32'($past(phase_accum) + $past(phase_inc)));
  a_phase_syn_update:    assert property (phase_syn   == ($past(phase_accum) + $past(phase_err_int)));
  a_phase_diff_comb:     assert property (phase_diff  == (phase_ref - phase_syn));
  // Given RTL compares unsigned >= 0, the else-path is unreachable; assert effective behavior
  a_phase_err_int_update:assert property (phase_err_int == 32'($past(phase_err_int) + $past(phase_err_filt)));
  a_vco_freq_update:     assert property (vco_freq == $past(vco_ctrl_filt));
  a_vco_div_comb:        assert property (vco_freq_div == (vco_freq / (2**16)));
  a_clk_toggle:          assert property (!$isunknown($past(clk_syn)) |-> clk_syn == ~$past(clk_syn));
  a_phase_ref_stable:    assert property ($stable(phase_ref));

  // Monotonicity of phase_inc w.r.t. ctrl_reg
  a_phase_inc_monotonic: assert property (($past(ctrl_reg) <= ctrl_reg) |-> $past(phase_inc) <= phase_inc);

  // No-X after first enabled cycle on key signals
  a_no_x_core: assert property (!$isunknown({ctrl_reg, phase_inc, phase_accum, phase_syn, phase_diff,
                                            phase_err_int, vco_freq, vco_freq_div, clk_syn})));

  // Coverage
  c_ctrl_min:        cover property (ctrl_reg == 8'h00);
  c_ctrl_max:        cover property (ctrl_reg == 8'hFF);
  c_clk_toggles:     cover property (!$isunknown($past(clk_syn)) && clk_syn == ~$past(clk_syn));
  c_phase_wrap:      cover property (phase_accum < $past(phase_accum));
  c_vco_updates:     cover property (vco_freq != $past(vco_freq));

endmodule