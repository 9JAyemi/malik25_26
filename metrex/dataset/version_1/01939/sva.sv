// SVA for chatgpt_generate_JC_counter
// Bindable checker that verifies reset, shift behavior, next_state usage, and X-safety.

module chatgpt_generate_JC_counter_sva;
  // Access DUT internals directly via bind scope
  // Signals assumed from bound instance: clk, rst_n, Q, shift_reg, next_state

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // X-safety when out of reset
  ap_no_x: assert property (!$isunknown({Q, shift_reg}));

  // While in reset, regs are held at 0 (override default disable)
  ap_reset_hold: assert property (disable iff (1'b0) (!rst_n |-> (Q == 4'b0 && shift_reg == 64'b0)));

  // State transition: Q uses previous shift_reg taps, inverted
  ap_q_update: assert property (
    Q == ({$past(shift_reg)[0], $past(shift_reg)[31], $past(shift_reg)[47], $past(shift_reg)[55]} ^ 4'hF)
  );

  // Shift register update: shift left and append previous Q[3]
  ap_shift_update: assert property (
    shift_reg == { $past(shift_reg[62:0]), $past(Q[3]) }
  );

  // Q equals next_state computed in prior cycle
  ap_q_matches_past_next_state: assert property (
    $past(rst_n) |-> (Q == $past(next_state))
  );

  // next_state (as computed) matches function of prior shift_reg
  ap_past_next_state_func: assert property (
    $past(rst_n) |-> ($past(next_state) ==
      ({$past(shift_reg)[0], $past(shift_reg)[31], $past(shift_reg)[47], $past(shift_reg)[55]} ^ 4'hF))
  );

  // Coverage

  // Reset deassert observed
  cv_reset_deassert: cover property ($rose(rst_n));

  // Both append cases observed into shift_reg[0]
  cv_append_0: cover property ($past(rst_n) && ($past(Q[3]) == 1'b0) && (shift_reg[0] == 1'b0));
  cv_append_1: cover property ($past(rst_n) && ($past(Q[3]) == 1'b1) && (shift_reg[0] == 1'b1));

  // Extremes of tap vector seen (all-0 -> Q=F, all-1 -> Q=0)
  cv_tap_all0_to_QF: cover property (
    $past({shift_reg[0],shift_reg[31],shift_reg[47],shift_reg[55]}) == 4'b0000 && Q == 4'hF
  );
  cv_tap_all1_to_Q0: cover property (
    $past({shift_reg[0],shift_reg[31],shift_reg[47],shift_reg[55]}) == 4'b1111 && Q == 4'h0
  );

  // Q changes at least once in operation
  cv_q_changes: cover property ($changed(Q));
endmodule

bind chatgpt_generate_JC_counter chatgpt_generate_JC_counter_sva u_chatgpt_generate_JC_counter_sva();