// SVA for my_or4b: X must equal (A | B | C | ~D_N). Includes key corner-case coverage.
// Bind this file to the DUT with the bind statement at bottom.

module my_or4b_sva (
  input logic A, B, C, D_N,
  input logic X
);

  // Functional equivalence on known inputs
  property p_func_eq;
    @(*) !$isunknown({A,B,C,D_N}) |-> (X === (A | B | C | ~D_N));
  endproperty
  a_func_eq: assert property (p_func_eq);

  // Necessity: if X is low (and all known), inputs must be A=B=C=0 and D_N=1
  a_low_implies_only_false_minterm: assert property
    (@(*) (!$isunknown({A,B,C,D_N,X}) && (X==1'b0)) |-> (A==0 && B==0 && C==0 && D_N==1));

  // Coverage: single-source highs and the only-low case
  c_A_only:       cover property (@(*) (A==1 && B==0 && C==0 && D_N==1 && X==1));
  c_B_only:       cover property (@(*) (A==0 && B==1 && C==0 && D_N==1 && X==1));
  c_C_only:       cover property (@(*) (A==0 && B==0 && C==1 && D_N==1 && X==1));
  c_DN_low_only:  cover property (@(*) (A==0 && B==0 && C==0 && D_N==0 && X==1));
  c_all_low:      cover property (@(*) (A==0 && B==0 && C==0 && D_N==1 && X==0));

endmodule

// Bind into DUT
bind my_or4b my_or4b_sva u_my_or4b_sva (.A(A), .B(B), .C(C), .D_N(D_N), .X(X));