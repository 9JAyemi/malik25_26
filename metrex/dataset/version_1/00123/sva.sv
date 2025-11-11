// Bindable SVA for lo_adc. Bind with:  bind lo_adc lo_adc_sva b_sva();

module lo_adc_sva;
  // Sample on pck0; ignore cycles with unknown key state
  default clocking cb @(posedge pck0); endclocking
  default disable iff ($isunknown({clk_state,pck_divider,divisor,lf_field,ssp_dout,adc_d,to_arm_shiftreg}));

  // Structural/output equivalences
  a_const_zeros:    assert property (pwr_oe1==1'b0 && pwr_hi==1'b0 && pwr_oe2==1'b0 && pwr_oe4==1'b0);
  a_ssp_clk_eq:     assert property (ssp_clk == pck0);
  a_dbg_eq:         assert property (dbg == adc_clk);
  a_adcclk_inv:     assert property (adc_clk == !clk_state);
  a_pwr_lo_def:     assert property (pwr_lo  == (!ssp_dout && lf_field && clk_state));
  a_pwr_oe3_def:    assert property (pwr_oe3 == (ssp_dout && !lf_field));
  a_din_gate_def:   assert property (ssp_din == (to_arm_shiftreg[7] && !clk_state));
  a_frame_def:      assert property (ssp_frame == ((pck_divider[7:3] == 5'd1) && !clk_state));
  a_mod_exclusive:  assert property (!(pwr_lo && pwr_oe3));
  a_din_clk1_low:   assert property (clk_state |-> !ssp_din);
  a_frame_clk1_low: assert property (clk_state |-> !ssp_frame);

  // Divider behavior
  a_div_inc:        assert property ((pck_divider != divisor)
                                     |=> (pck_divider == $past(pck_divider)+8'd1) && (clk_state == $past(clk_state)));
  a_div_wrap_tgl:   assert property ((pck_divider == divisor)
                                     |=> (pck_divider == 8'd0) && (clk_state == !$past(clk_state)));

  // Shifter behavior
  a_capture_load:   assert property (((pck_divider == 8'd7) && !clk_state)
                                     |=> (to_arm_shiftreg == $past(adc_d)));
  a_shift_right:    assert property (!((pck_divider == 8'd7) && !clk_state)
                                     |=> (to_arm_shiftreg[7:1] == $past(to_arm_shiftreg[6:0])
                                          && to_arm_shiftreg[0] == 1'b0));

  // Useful coverage
  c_wrap:           cover property ((pck_divider == divisor) ##1 (pck_divider == 8'd0 && clk_state == !$past(clk_state)));
  c_capture:        cover property ((pck_divider == 8'd7) && !clk_state);
  c_frame_hi:       cover property (ssp_frame);
  c_din_hi:         cover property (ssp_din);
  c_pwr_lo_hi:      cover property (pwr_lo);
  c_pwr_oe3_hi:     cover property (pwr_oe3);
endmodule