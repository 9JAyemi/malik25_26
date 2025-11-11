// SVA for fpu_round
module fpu_round_sva;
  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Decode/constant checks
  ap_round_amt_const: assert property (rounding_amount == 56'd4);
  ap_mode_onehot:     assert property ($onehot({round_nearest, round_to_zero, round_to_pos_inf, round_to_neg_inf}));
  ap_trigger_def: assert property (
    round_trigger ==
      ((round_nearest && mantissa_term[1]) ||
       (round_to_pos_inf && !sign_term && (mantissa_term[1:0] != 2'b00)) ||
       (round_to_neg_inf &&  sign_term && (mantissa_term[1:0] != 2'b00)))
  );
  ap_to_zero_no_round: assert property (round_to_zero |-> !round_trigger);

  // Pipeline/data-path checks
  ap_sum_round:    assert property ($past(!rst) |-> sum_round == ($past(mantissa_term) + 56'd4));
  ap_sum_round_2:  assert property (sum_round_2 == ($past(sum_round)[55] ? ($past(sum_round) >> 1) : $past(sum_round)));
  ap_exp_round:    assert property (exponent_round == ($past(sum_round)[55] ? (exponent_term + 12'd1) : exponent_term));
  ap_passthru:     assert property (!round_trigger |-> (sum_final == mantissa_term && exponent_final == exponent_term));
  ap_use_rounded:  assert property ( round_trigger |-> (sum_final == sum_round_2 && exponent_final == exponent_round));
  ap_pack:         assert property (round_out == {sign_term, exponent_final[10:0], sum_final[53:2]});

  // Mode-specific trigger behaviors
  ap_nearest_trig: assert property (round_nearest  |-> (round_trigger == mantissa_term[1]));
  ap_posinf_trig:  assert property (round_to_pos_inf |-> (round_trigger == (!sign_term && |mantissa_term[1:0])));
  ap_neginf_trig:  assert property (round_to_neg_inf |-> (round_trigger == ( sign_term && |mantissa_term[1:0])));

  // Reset/X safety
  ap_reset_clears: assert property (rst |=> (sum_round==0 && sum_round_2==0 && exponent_round==0 &&
                                             sum_final==0 && exponent_final==0 && round_out==0));
  ap_no_x_out:     assert property (!$isunknown({round_out, exponent_final}));

  // Coverage
  cp_mode_nearest: cover property (round_mode==2'b00);
  cp_mode_zero:    cover property (round_mode==2'b01);
  cp_mode_posinf:  cover property (round_mode==2'b10);
  cp_mode_neginf:  cover property (round_mode==2'b11);

  cp_nearest_round:     cover property (round_nearest && mantissa_term[1] && round_trigger);
  cp_nearest_passthru:  cover property (round_nearest && !mantissa_term[1] && !round_trigger);
  cp_posinf_round:      cover property (round_to_pos_inf && !sign_term && |mantissa_term[1:0] && round_trigger);
  cp_posinf_passthru:   cover property (round_to_pos_inf &&  sign_term && |mantissa_term[1:0] && !round_trigger);
  cp_neginf_round:      cover property (round_to_neg_inf &&  sign_term && |mantissa_term[1:0] && round_trigger);
  cp_neginf_passthru:   cover property (round_to_neg_inf && !sign_term && |mantissa_term[1:0] && !round_trigger);
  cp_zero_passthru:     cover property (round_to_zero && |mantissa_term[1:0] && !round_trigger);

  cp_overflow_rounded:    cover property ($past(!rst) && $past(sum_round)[55]  && round_trigger);
  cp_no_overflow_rounded: cover property ($past(!rst) && !$past(sum_round)[55] && round_trigger);
  cp_pack_changes:        cover property (round_trigger && (round_out != $past(round_out)));
endmodule

bind fpu_round fpu_round_sva sva();