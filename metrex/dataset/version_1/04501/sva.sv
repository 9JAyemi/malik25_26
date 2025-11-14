// SVA for priority_mux
// Bind this file to the DUT

module priority_mux_sva (
  input logic A,
  input logic B,
  input logic C,
  input logic S,
  input logic P,
  input logic Y
);

  default clocking cb @(*) endclocking

  // Golden function
  let exp = (P ? C : (S ? B : A));

  // Functional equivalence when inputs are known
  a_func:     assert property ( (!$isunknown({A,B,C,S,P})) |-> (Y == exp) )
               else $error("priority_mux: functional mismatch");
  // No X/Z on Y when inputs are known
  a_known:    assert property ( (!$isunknown({A,B,C,S,P})) |-> !$isunknown(Y) )
               else $error("priority_mux: Y unknown while inputs known");

  // Priority correctness (redundant with a_func but precise and readable)
  a_P:        assert property ( P          |-> (Y == C) );
  a_S:        assert property ( !P && S    |-> (Y == B) );
  a_A:        assert property ( !P && !S   |-> (Y == A) );

  // Influence: selected data must drive Y immediately when selection stable
  a_inf_C:    assert property ( P          && $changed(C) |-> (Y == C) );
  a_inf_B:    assert property ( !P && S    && $changed(B) |-> (Y == B) );
  a_inf_A:    assert property ( !P && !S   && $changed(A) |-> (Y == A) );

  // Independence: unselected inputs must not affect Y
  a_ind_P:    assert property ( P && $stable(C) && ($changed(A) || $changed(B) || $changed(S))
                                |-> $stable(Y) );
  a_ind_S:    assert property ( !P && S && $stable(B) && ($changed(A) || $changed(C))
                                |-> $stable(Y) );
  a_ind_A:    assert property ( !P && !S && $stable(A) && ($changed(B) || $changed(C))
                                |-> $stable(Y) );

  // Coverage: exercise each path and data-driven toggles
  c_path_P0:  cover property ( P        && (Y == C) && (C == 0) );
  c_path_P1:  cover property ( P        && (Y == C) && (C == 1) );
  c_path_S0:  cover property ( !P && S  && (Y == B) && (B == 0) );
  c_path_S1:  cover property ( !P && S  && (Y == B) && (B == 1) );
  c_path_A0:  cover property ( !P && !S && (Y == A) && (A == 0) );
  c_path_A1:  cover property ( !P && !S && (Y == A) && (A == 1) );

  c_toggle_C: cover property ( P        && $changed(C) && $changed(Y) );
  c_toggle_B: cover property ( !P && S  && $changed(B) && $changed(Y) );
  c_toggle_A: cover property ( !P && !S && $changed(A) && $changed(Y) );

endmodule

bind priority_mux priority_mux_sva sva_i (
  .A(A), .B(B), .C(C), .S(S), .P(P), .Y(Y)
);