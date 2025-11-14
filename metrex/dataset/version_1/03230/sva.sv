// SVA for sky130_fd_sc_hdll__or4b: X = A | B | C | ~D_N
module sky130_fd_sc_hdll__or4b_sva (
  input logic A, B, C, D_N, X
);
  default clocking cb @ (posedge $global_clock); endclocking

  // Golden functional check (4-state aware)
  assert property (X === (A | B | C | ~D_N));

  // Deterministic cases
  assert property ((A===1'b0 && B===1'b0 && C===1'b0 && D_N===1'b1) |-> (X===1'b0));
  assert property (((A===1'b1) || (B===1'b1) || (C===1'b1) || (D_N===1'b0)) |-> (X===1'b1));

  // No X on output when inputs are all known
  assert property (!$isunknown({A,B,C,D_N}) |-> !$isunknown(X));

  // Functional coverage (key minterms)
  cover property (A===1'b0 && B===1'b0 && C===1'b0 && D_N===1'b1 && X===1'b0); // all-off -> 0
  cover property (A===1'b1 && B===1'b0 && C===1'b0 && D_N===1'b1 && X===1'b1); // A-only -> 1
  cover property (A===1'b0 && B===1'b1 && C===1'b0 && D_N===1'b1 && X===1'b1); // B-only -> 1
  cover property (A===1'b0 && B===1'b0 && C===1'b1 && D_N===1'b1 && X===1'b1); // C-only -> 1
  cover property (A===1'b0 && B===1'b0 && C===1'b0 && D_N===1'b0 && X===1'b1); // D_N low -> 1

  // Simple toggle coverage from base state
  sequence base0; A===1'b0 && B===1'b0 && C===1'b0 && D_N===1'b1 && X===1'b0; endsequence
  cover property (base0 ##1 (A===1'b1 && B===1'b0 && C===1'b0 && D_N===1'b1 && X===1'b1)); // A rise -> X rise
  cover property (base0 ##1 (A===1'b0 && B===1'b0 && C===1'b0 && D_N===1'b0 && X===1'b1)); // D_N fall -> X rise
endmodule

bind sky130_fd_sc_hdll__or4b sky130_fd_sc_hdll__or4b_sva (.A(A), .B(B), .C(C), .D_N(D_N), .X(X));