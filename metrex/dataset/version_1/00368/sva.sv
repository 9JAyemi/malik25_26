// SVA for shift_addsub. Bind this file to the DUT.
// Focused, high-value checks and essential coverage.

module shift_addsub_sva;
  default clocking cb @(posedge clk); endclocking

  // Reset behavior
  a_reset_zero: assert property (reset |-> (Q==4'h0 && shifted_Q==4'h0));
  a_reset_release_clear: assert property ($fell(reset) |-> (Q==4'h0 && shifted_Q==4'h0));

  // Shift-register relation (SHIFT <= LOAD == Q, one-cycle later)
  a_shift_follow: assert property (disable iff (reset) shifted_Q == $past(Q));

  // Q next-state = two's-comp(A) + shifted_Q (low 4 bits)
  a_q_next: assert property (disable iff (reset)
                             Q == $past( ( ((~A) + 4'd1) + shifted_Q ) & 4'hF ));

  // Combinational ALU correctness as used in the DUT
  a_subbedA_func: assert property ( subbed_A == ( ((~A) + 4'd1 + shifted_Q) & 4'hF ) );
  a_addedA_func:  assert property ( added_A  == ( sub ? subbed_A
                                                     : ((A + shifted_Q) & 4'hF) ) );
  a_result_func:  assert property ( result   == ( sub ? ( ((~A) + 4'd1 + shifted_Q) & 4'hF )
                                                     : ( (A     +       shifted_Q) & 4'hF ) ) );

  // When previous op was subtract, Q equals previous result
  a_q_eq_prev_result_on_sub: assert property (disable iff (reset) $past(sub) |-> Q == $past(result));

  // No X-propagation out of reset
  a_no_x: assert property (disable iff (reset) !$isunknown({Q, shifted_Q, result, added_A, subbed_A}));

  // Top-level input B is unused: changes must not affect state/output
  a_B_unused: assert property (disable iff (reset) $changed(B) |-> $stable({result, Q}));

  // Coverage
  c_add_mode:  cover property (disable iff (reset) !sub && result == ((A + shifted_Q) & 4'hF));
  c_sub_mode:  cover property (disable iff (reset)  sub && result == (((~A) + 4'd1 + shifted_Q) & 4'hF));
  c_add_wrap:  cover property (disable iff (reset) !sub && (A + shifted_Q) > 4'hF);
  c_sub_wrap:  cover property (disable iff (reset)  sub && (((~A) + 4'd1 + shifted_Q) > 4'hF));
  c_shift_lag: cover property (disable iff (reset) $changed(Q) ##1 (shifted_Q == $past(Q)));
  c_reset_toggle: cover property ($rose(reset)); cover property ($fell(reset));
endmodule

bind shift_addsub shift_addsub_sva sva_inst();