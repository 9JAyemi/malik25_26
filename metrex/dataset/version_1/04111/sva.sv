// SVA for sky130_fd_sc_ls__and3b (X = B & C & ~A_N)
// Concise, port-only bind; functional checks, X-prop checks, and full truth-table coverage.

checker and3b_sva (input logic A_N, B, C, X);
  // Sample on any input edge; use ##0 to observe post-settle value in same time slot
  default clocking cb @(
      posedge A_N or negedge A_N or
      posedge B   or negedge B   or
      posedge C   or negedge C
  ); endclocking

  // Functional equivalence
  assert property (1'b1 |-> ##0 (X === (B & C & ~A_N)));

  // Known output when inputs are known
  assert property ((!$isunknown({A_N,B,C})) |-> ##0 (!$isunknown(X)));

  // Observability: if X is 1, inputs must be B=1, C=1, A_N=0
  assert property (X === 1'b1 |-> ##0 (B && C && !A_N));

  // Edge coverage on output
  cover property ($rose(X));
  cover property ($fell(X));

  // Full truth-table coverage (all 8 input combos with expected X)
  cover property (##0 (A_N===1'b0 && B===1'b0 && C===1'b0 && X===1'b0));
  cover property (##0 (A_N===1'b0 && B===1'b0 && C===1'b1 && X===1'b0));
  cover property (##0 (A_N===1'b0 && B===1'b1 && C===1'b0 && X===1'b0));
  cover property (##0 (A_N===1'b0 && B===1'b1 && C===1'b1 && X===1'b1)); // only 1 case
  cover property (##0 (A_N===1'b1 && B===1'b0 && C===1'b0 && X===1'b0));
  cover property (##0 (A_N===1'b1 && B===1'b0 && C===1'b1 && X===1'b0));
  cover property (##0 (A_N===1'b1 && B===1'b1 && C===1'b0 && X===1'b0));
  cover property (##0 (A_N===1'b1 && B===1'b1 && C===1'b1 && X===1'b0));

  // Input toggle coverage
  cover property ($rose(A_N)); cover property ($fell(A_N));
  cover property ($rose(B));   cover property ($fell(B));
  cover property ($rose(C));   cover property ($fell(C));
endchecker

bind sky130_fd_sc_ls__and3b and3b_sva and3b_sva_i (.A_N(A_N), .B(B), .C(C), .X(X));