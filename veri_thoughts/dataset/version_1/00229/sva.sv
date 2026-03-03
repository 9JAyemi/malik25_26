// SVA for and4_nor
module and4_nor_sva (
  input Y, A, B, C, D,
  input not_A, not_B, not_C, not_D,
  input nor0_out, nor1_out,
  input buf0_out
);

  // Sample on any input edge; use ##0 to avoid preponed sampling issues
  default clocking cb @(
    posedge A or negedge A or
    posedge B or negedge B or
    posedge C or negedge C or
    posedge D or negedge D
  ); endclocking

  // Functional equivalence (when inputs are known)
  a_func:    assert property (!$isunknown({A,B,C,D}) |-> ##0
                               (Y == (D & ((A & B) | ~C))));

  // Structural chain (when inputs are known)
  a_struct:  assert property (!$isunknown({A,B,C,D}) |-> ##0
                               (not_A == ~A &&
                                not_B == ~B &&
                                not_C == ~C &&
                                not_D == ~D &&
                                nor0_out == ~(not_A | not_B) &&
                                nor1_out == ~(nor0_out | not_C) &&
                                Y == ~(nor1_out | not_D) &&
                                buf0_out === Y));

  // Known-propagation: no Xs internally if inputs are known
  a_known:   assert property (!$isunknown({A,B,C,D}) |-> ##0
                               !$isunknown({not_A,not_B,not_C,not_D,
                                            nor0_out,nor1_out,Y,buf0_out}));

  // Key implications (concise sanity checks)
  a_d0:      assert property (!$isunknown(D)        && (D==0)     |-> ##0 (Y==0));
  a_c0:      assert property (!$isunknown({D,C})    && (D && !C)  |-> ##0 (Y==1));
  a_c1ab:    assert property (!$isunknown({D,C,A,B})&& (D && C)   |-> ##0 (Y==(A & B)));

  // Toggle coverage
  c_a_r: cover property ($rose(A));   c_a_f: cover property ($fell(A));
  c_b_r: cover property ($rose(B));   c_b_f: cover property ($fell(B));
  c_c_r: cover property ($rose(C));   c_c_f: cover property ($fell(C));
  c_d_r: cover property ($rose(D));   c_d_f: cover property ($fell(D));
  c_y_r: cover property (##0 $rose(Y));
  c_y_f: cover property (##0 $fell(Y));

  // Functional corner coverage
  c_y1_c0:  cover property (D && !C);
  c_y1_ab:  cover property (D && C && A && B);
  c_y0_d0:  cover property (!D);
  c_y0_ab0: cover property (D && C && !(A && B));

endmodule

// Bind into DUT (internals are visible in bind scope)
bind and4_nor and4_nor_sva sva_i (
  .Y(Y), .A(A), .B(B), .C(C), .D(D),
  .not_A(not_A), .not_B(not_B), .not_C(not_C), .not_D(not_D),
  .nor0_out(nor0_out), .nor1_out(nor1_out),
  .buf0_out(buf0_out)
);