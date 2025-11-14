// SVA for FSM_Mult_Function
// Bind by module type so we can see internal state_reg/state_next/params
bind FSM_Mult_Function FSM_Mult_Function_sva();
module FSM_Mult_Function_sva;

  // Access DUT scope directly via bind
  // Default clock/reset
  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Basic health checks
  a_state_known:         assert property (!$isunknown(state_reg));
  a_outputs_known:       assert property (!$isunknown({
                                load_0_o,load_1_o,load_2_o,load_3_o,load_4_o,load_5_o,load_6_o,
                                ctrl_select_a_o,ctrl_select_b_o,selector_b_o,ctrl_select_c_o,
                                exp_op_o,shift_value_o,rst_int,ready}));

  // Async reset effect (sampled): if rst is 1 on a clock, state must be start
  a_reset_forces_start:  assert property (rst |-> state_reg == start);

  // State encoding range
  a_state_in_range:      assert property (state_reg inside {
                                start, load_operands, extra64_1, add_exp, subt_bias,
                                mult_overf, mult_norn, mult_no_norn, round_case,
                                adder_round, round_norm, final_load, ready_flag});

  // Next-state transition checks
  a_start_hold:          assert property ((state_reg==start && !beg_FSM) |=> state_reg==start);
  a_start_begin:         assert property ((state_reg==start &&  beg_FSM) |=> state_reg==load_operands);

  a_load_operands:       assert property ((state_reg==load_operands) |=> state_reg==extra64_1);
  a_extra64_1:           assert property ((state_reg==extra64_1)   |=> state_reg==add_exp);
  a_add_exp:             assert property ((state_reg==add_exp)     |=> state_reg==subt_bias);

  a_subt_bias_zero:      assert property ((state_reg==subt_bias &&  zero_flag_i) |=> state_reg==ready_flag);
  a_subt_bias_nzero:     assert property ((state_reg==subt_bias && !zero_flag_i) |=> state_reg==mult_overf);

  a_mult_overf_shift:    assert property ((state_reg==mult_overf &&  Mult_shift_i) |=> state_reg==mult_norn);
  a_mult_overf_nshift:   assert property ((state_reg==mult_overf && !Mult_shift_i) |=> state_reg==mult_no_norn);

  a_mult_norn:           assert property ((state_reg==mult_norn)     |=> state_reg==round_case);
  a_mult_no_norn:        assert property ((state_reg==mult_no_norn)  |=> state_reg==round_case);

  a_round_case_rnd:      assert property ((state_reg==round_case &&  round_flag_i) |=> state_reg==adder_round);
  a_round_case_nrnd:     assert property ((state_reg==round_case && !round_flag_i) |=> state_reg==final_load);

  a_adder_round:         assert property ((state_reg==adder_round) |=> state_reg==round_norm);
  a_round_norm:          assert property ((state_reg==round_norm)  |=> state_reg==final_load);
  a_final_load:          assert property ((state_reg==final_load)  |=> state_reg==ready_flag);

  a_ready_hold:          assert property ((state_reg==ready_flag && !ack_FSM) |=> state_reg==ready_flag);
  a_ready_ack:           assert property ((state_reg==ready_flag &&  ack_FSM) |=> state_reg==start);

  // Per-state output checks (only assert what's mandated)
  a_start_outputs:       assert property ((state_reg==start) |-> (rst_int && !ready));

  a_load_operands_o:     assert property ((state_reg==load_operands) |-> load_0_o);

  a_add_exp_o:           assert property ((state_reg==add_exp) |-> (load_1_o && load_2_o &&
                                                                    ctrl_select_a_o &&
                                                                    ctrl_select_b_o && selector_b_o==2'b01));

  a_subt_bias_o:         assert property ((state_reg==subt_bias) |-> (load_2_o && load_3_o && exp_op_o));

  a_mult_overf_o1:       assert property ((state_reg==mult_overf &&  Mult_shift_i) |-> (ctrl_select_b_o && selector_b_o==2'b10));
  a_mult_overf_o0:       assert property ((state_reg==mult_overf && !Mult_shift_i) |-> (!ctrl_select_b_o && selector_b_o==2'b00));

  a_mult_norn_o:         assert property ((state_reg==mult_norn) |-> (shift_value_o && load_6_o && load_2_o && load_3_o));
  a_mult_no_norn_o:      assert property ((state_reg==mult_no_norn) |-> (!shift_value_o && load_6_o));

  a_round_case_o:        assert property ((state_reg==round_case && round_flag_i) |-> ctrl_select_c_o);

  a_adder_round_o:       assert property ((state_reg==adder_round) |-> (load_4_o && ctrl_select_b_o && selector_b_o==2'b01));

  a_round_norm_o_ovf:    assert property ((state_reg==round_norm &&  Add_Overflow_i) |-> (shift_value_o && load_2_o && load_3_o && load_6_o));
  a_round_norm_o_noovf:  assert property ((state_reg==round_norm && !Add_Overflow_i) |-> (!shift_value_o && load_6_o));

  a_final_load_o:        assert property ((state_reg==final_load) |-> load_5_o);
  a_ready_flag_o:        assert property ((state_reg==ready_flag) |-> ready);

  // "Only-in-state" implications to catch stray asserts
  a_ready_only_in_ready: assert property (ready      |-> state_reg==ready_flag);
  a_rstint_only_in_start:assert property (rst_int    |-> state_reg==start);
  a_ld0_only_in_loadop:  assert property (load_0_o   |-> state_reg==load_operands);
  a_ld4_only_in_ar:      assert property (load_4_o   |-> state_reg==adder_round);
  a_ld5_only_in_final:   assert property (load_5_o   |-> state_reg==final_load);
  a_csela_only_in_add:   assert property (ctrl_select_a_o |-> state_reg==add_exp);
  a_cselc_only_in_rcase: assert property (ctrl_select_c_o |-> (state_reg==round_case && round_flag_i));
  a_cselb_scope:         assert property (ctrl_select_b_o |-> (
                                            (state_reg==add_exp) ||
                                            (state_reg==adder_round) ||
                                            (state_reg==mult_overf && Mult_shift_i)));
  a_selb_zero_when_cselb0:assert property ((!ctrl_select_b_o) |-> selector_b_o==2'b00);
  a_shift_only_where_valid:assert property (shift_value_o |-> (
                                            (state_reg==mult_norn) ||
                                            (state_reg==round_norm && Add_Overflow_i)));

  // Functional coverage
  c_zero_short_path:     cover property (state_reg==start ##1 beg_FSM ##1
                                         load_operands ##1 extra64_1 ##1 add_exp ##1
                                         subt_bias ##1 (zero_flag_i) ##1 ready_flag);

  c_norm_round_ovf:      cover property (state_reg==start ##1 beg_FSM ##1
                                         load_operands ##1 extra64_1 ##1 add_exp ##1
                                         subt_bias ##1 (!zero_flag_i) ##1 mult_overf ##1
                                         (Mult_shift_i) ##1 mult_norn ##1 round_case ##1
                                         (round_flag_i) ##1 adder_round ##1 round_norm ##1
                                         (Add_Overflow_i) ##1 final_load ##1 ready_flag);

  c_nonorm_noround:      cover property (state_reg==start ##1 beg_FSM ##1
                                         load_operands ##1 extra64_1 ##1 add_exp ##1
                                         subt_bias ##1 (!zero_flag_i) ##1 mult_overf ##1
                                         (!Mult_shift_i) ##1 mult_no_norn ##1 round_case ##1
                                         (!round_flag_i) ##1 final_load ##1 ready_flag);

  c_ack_handshake:       cover property (state_reg==ready_flag ##1 ack_FSM ##1 state_reg==start);

endmodule