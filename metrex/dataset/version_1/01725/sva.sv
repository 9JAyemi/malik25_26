// SVA for sky130_fd_sc_lp__or3b (X = A | B | ~C_N)
`ifndef SKY130_FD_SC_LP__OR3B_SVA
`define SKY130_FD_SC_LP__OR3B_SVA

module sky130_fd_sc_lp__or3b_sva (
  input logic A, B, C_N, X
);

  // Trigger on any relevant edge
  default clocking cb @(
    posedge A or negedge A or
    posedge B or negedge B or
    posedge C_N or negedge C_N or
    posedge X or negedge X
  ); endclocking

  // Functional equivalence
  a_func:        assert property (X === (A || B || !C_N));

  // No X/Z on output when inputs are known
  a_no_x_out:    assert property ((!$isunknown({A,B,C_N})) |-> (!$isunknown(X)));

  // Cause-effect: activating edges force X high
  a_a_rise_sets: assert property ($rose(A)   |-> ##0 (X===1'b1));
  a_b_rise_sets: assert property ($rose(B)   |-> ##0 (X===1'b1));
  a_cn_fall_sets:assert property ($fell(C_N) |-> ##0 (X===1'b1));

  // Low corner
  a_low_corner:  assert property ((A==1'b0 && B==1'b0 && C_N==1'b1) |-> (X===1'b0));

  // Truth-table coverage (all 8 input combos and expected X)
  c_000: cover property ((A==0 && B==0 && C_N==1) && (X==0));
  c_001: cover property ((A==0 && B==0 && C_N==0) && (X==1));
  c_010: cover property ((A==0 && B==1 && C_N==1) && (X==1));
  c_011: cover property ((A==0 && B==1 && C_N==0) && (X==1));
  c_100: cover property ((A==1 && B==0 && C_N==1) && (X==1));
  c_101: cover property ((A==1 && B==0 && C_N==0) && (X==1));
  c_110: cover property ((A==1 && B==1 && C_N==1) && (X==1));
  c_111: cover property ((A==1 && B==1 && C_N==0) && (X==1));

  // Toggle coverage on X
  c_x_rise: cover property ($rose(X));
  c_x_fall: cover property ($fell(X));

  // Edge-to-effect coverage
  c_a_rise_sets:  cover property ($rose(A)   ##0 (X==1));
  c_b_rise_sets:  cover property ($rose(B)   ##0 (X==1));
  c_cn_fall_sets: cover property ($fell(C_N) ##0 (X==1));

endmodule

// Bind into the DUT
bind sky130_fd_sc_lp__or3b sky130_fd_sc_lp__or3b_sva u_sva (
  .A(A), .B(B), .C_N(C_N), .X(X)
);

`endif