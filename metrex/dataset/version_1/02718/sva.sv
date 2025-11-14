// SVA for and_gate
module and_gate_sva (input logic A, B, X);
  // Sample on any input edge
  default clocking cb @(posedge A or negedge A or posedge B or negedge B); endclocking

  // Functional correctness (4-state accurate)
  a_and_func: assert property (X === (A & B));

  // Output stable when inputs are stable
  a_stable:   assert property ($stable({A,B}) |-> $stable(X));

  // If inputs are known, output must be known
  a_known_out: assert property (! $isunknown({A,B}) |-> ! $isunknown(X));

  // Truth-table coverage
  c_tt_00: cover property (A===1'b0 && B===1'b0 && X===1'b0);
  c_tt_01: cover property (A===1'b0 && B===1'b1 && X===1'b0);
  c_tt_10: cover property (A===1'b1 && B===1'b0 && X===1'b0);
  c_tt_11: cover property (A===1'b1 && B===1'b1 && X===1'b1);

  // Toggle coverage on output
  c_x_rise: cover property ($rose(X));
  c_x_fall: cover property ($fell(X));
endmodule

bind and_gate and_gate_sva u_and_gate_sva(.A(A), .B(B), .X(X));