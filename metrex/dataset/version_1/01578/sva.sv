// SVA checker bound into DUT
module gray_code_counter_sva;

  default clocking cb @(posedge clk); endclocking

  // Reset behavior
  a_reset_clears: assert property (reset |=> (q0==1'b0 && q1==1'b0 && q2==1'b0));
  a_hold_zero_during_reset: assert property (reset && $past(reset) |-> (q0==1'b0 && q1==1'b0 && q2==1'b0));

  // Sanity (no X/Z out of reset)
  a_no_x_out_of_reset: assert property (!reset |-> !$isunknown({q2,q1,q0}));

  // Hold when disabled
  a_hold_when_disabled: assert property (disable iff (reset)
                                         (!enable) |=> {q2,q1,q0} == $past({q2,q1,q0}));

  // Functional next-state when enabled
  a_next_when_enabled: assert property (disable iff (reset)
                                        (enable) |=> (q0 == $past(q0 ^ q1) &&
                                                      q1 == $past(q1 ^ q2) &&
                                                      q2 == $past(q2 ^ enable)));

  // Internal pipeline registers match computed values when used
  a_d_regs_match: assert property (disable iff (reset)
                                   (enable) |=> (d0 == $past(q0 ^ q1) &&
                                                 d1 == $past(q1 ^ q2) &&
                                                 d2 == $past(q2 ^ enable)));

  // Gray property: exactly one bit changes on enabled steps
  a_gray_one_bit_change: assert property (disable iff (reset)
                                          (enable) |=> $countones({q2,q1,q0} ^ $past({q2,q1,q0})) == 1);

  // Coverage
  c_saw_reset:   cover property (reset);
  c_saw_enable:  cover property (disable iff (reset) enable);
  c_gray_step:   cover property (disable iff (reset)
                                 enable |=> $countones({q2,q1,q0} ^ $past({q2,q1,q0})) == 1);
  c_q0_toggled:  cover property (disable iff (reset) enable && (q0 ^ $past(q0)));
  c_q1_toggled:  cover property (disable iff (reset) enable && (q1 ^ $past(q1)));
  c_q2_toggled:  cover property (disable iff (reset) enable && (q2 ^ $past(q2)));

  genvar s;
  generate
    for (s=0; s<8; s++) begin : cov_states
      c_state: cover property (disable iff (reset) {q2,q1,q0} == s[2:0]);
    end
  endgenerate

endmodule

bind gray_code_counter gray_code_counter_sva gc_sva();