// SVA for sky130_fd_sc_hd__and3
// Bind this file to the DUT to check and cover its behavior.

module sky130_fd_sc_hd__and3_sva (
  input logic A,
  input logic B,
  input logic C,
  input logic X
);

  // Sample on any input edge
  default clocking cb_in @(posedge A or negedge A or
                           posedge B or negedge B or
                           posedge C or negedge C); endclocking

  // Functional equivalence (4-state aware)
  ap_func: assert property (X === (A & B & C));

  // No unknown on output when inputs are known
  ap_known: assert property (!$isunknown({A,B,C}) |-> !$isunknown(X));

  // Truth-table coverage (inputs and resulting X)
  cv_000: cover property (A===1'b0 && B===1'b0 && C===1'b0 && X===1'b0);
  cv_001: cover property (A===1'b0 && B===1'b0 && C===1'b1 && X===1'b0);
  cv_010: cover property (A===1'b0 && B===1'b1 && C===1'b0 && X===1'b0);
  cv_011: cover property (A===1'b0 && B===1'b1 && C===1'b1 && X===1'b0);
  cv_100: cover property (A===1'b1 && B===1'b0 && C===1'b0 && X===1'b0);
  cv_101: cover property (A===1'b1 && B===1'b0 && C===1'b1 && X===1'b0);
  cv_110: cover property (A===1'b1 && B===1'b1 && C===1'b0 && X===1'b0);
  cv_111: cover property (A===1'b1 && B===1'b1 && C===1'b1 && X===1'b1);

  // Unknown propagation coverage
  cv_xprop: cover property ($isunknown({A,B,C}) && $isunknown(X));

endmodule

// Bind into the DUT definition
bind sky130_fd_sc_hd__and3 sky130_fd_sc_hd__and3_sva and3_sva_i (
  .A(A), .B(B), .C(C), .X(X)
);