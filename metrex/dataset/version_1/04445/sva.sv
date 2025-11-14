// SVA for mux2to1
module mux2to1_sva (
  input logic A,
  input logic B,
  input logic S,
  input logic Y
);

  // Functional correctness and no-X when inputs known
  a_func:   assert property (@(*) (!$isunknown({S,A,B})) |-> (Y == (S ? B : A)));
  a_no_x:   assert property (@(*) (!$isunknown({S,A,B})) |-> !$isunknown(Y));

  // Isolation: unselected input must not affect Y
  a_iso_b:  assert property (@(*) (S===1'b0 && !$isunknown({A,S}) && $changed(B)) |-> $stable(Y));
  a_iso_a:  assert property (@(*) (S===1'b1 && !$isunknown({B,S}) && $changed(A)) |-> $stable(Y));

  // X-propagation semantics
  a_xdiff:  assert property (@(*) (!$isunknown({A,B}) && (A!==B) && $isunknown(S)) |-> $isunknown(Y));
  a_xsame:  assert property (@(*) (!$isunknown({A,B}) && (A===B) && $isunknown(S)) |-> (Y===A));

  // Coverage: exercise both selects and data values
  cv_s0_a0: cover  property (@(*) (!$isunknown({S,A,B})) && S===1'b0 && A===1'b0 && Y===1'b0);
  cv_s0_a1: cover  property (@(*) (!$isunknown({S,A,B})) && S===1'b0 && A===1'b1 && Y===1'b1);
  cv_s1_b0: cover  property (@(*) (!$isunknown({S,A,B})) && S===1'b1 && B===1'b0 && Y===1'b0);
  cv_s1_b1: cover  property (@(*) (!$isunknown({S,A,B})) && S===1'b1 && B===1'b1 && Y===1'b1);

  // Coverage: select toggles
  cv_rise:  cover  property (@(*) (!$isunknown({S,A,B})) && $rose(S) && (Y===B));
  cv_fall:  cover  property (@(*) (!$isunknown({S,A,B})) && $fell(S) && (Y===A));

  // Coverage: X-propagation cases
  cv_xeq:   cover  property (@(*) (!$isunknown({A,B})) && (A===B) && $isunknown(S) && (Y===A));
  cv_xneq:  cover  property (@(*) (!$isunknown({A,B})) && (A!==B) && $isunknown(S) && $isunknown(Y));

endmodule

// Bind into DUT
bind mux2to1 mux2to1_sva u_mux2to1_sva (.A(A), .B(B), .S(S), .Y(Y));