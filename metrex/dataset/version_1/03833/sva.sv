// SVA for sky130_fd_sc_lp__or2b
// Function: X = A | ~B_N

`ifndef SKY130_FD_SC_LP__OR2B_SVA
`define SKY130_FD_SC_LP__OR2B_SVA

module sky130_fd_sc_lp__or2b_sva;

  // Functional equivalence (4-state accurate)
  assert property (@(*) X === (A | ~B_N))
    else $error("or2b func mismatch: A=%b B_N=%b X=%b", A, B_N, X);

  // Power pins sanity
  assert property (@(*) (VPWR===1'b1 && VPB===1'b1 && VGND===1'b0 && VNB===1'b0))
    else $error("or2b power pins invalid: VPWR=%b VPB=%b VGND=%b VNB=%b", VPWR, VPB, VGND, VNB);

  // If inputs are known, output must be known
  assert property (@(*) (!$isunknown({A,B_N})) |-> !$isunknown(X))
    else $error("or2b X unknown with known inputs: A=%b B_N=%b X=%b", A, B_N, X);

  // Truth-table coverage
  cover property (@(*) (A===1'b0 && B_N===1'b1 && X===1'b0)); // 0,1 -> 0
  cover property (@(*) (A===1'b0 && B_N===1'b0 && X===1'b1)); // 0,0 -> 1
  cover property (@(*) (A===1'b1 && B_N===1'b1 && X===1'b1)); // 1,1 -> 1
  cover property (@(*) (A===1'b1 && B_N===1'b0 && X===1'b1)); // 1,0 -> 1

endmodule

bind sky130_fd_sc_lp__or2b sky130_fd_sc_lp__or2b_sva sva_or2b();

`endif