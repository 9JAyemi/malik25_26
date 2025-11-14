// SVA for xor_gate
module xor_gate_sva (input logic A, B, X);

  // Functional correctness (allowing 4-state equivalence); sampled after delta
  property p_func; @(A or B or X) ##0 (X === (A ^ B)); endproperty
  a_func: assert property (p_func);

  // Output must not change unless at least one input changes
  property p_no_spurious; @(X) ##0 ($changed(A) || $changed(B)); endproperty
  a_no_spurious: assert property (p_no_spurious);

  // If inputs are known, output must be known (no X/Z propagation)
  property p_known_in_known_out; @(A or B) (!$isunknown({A,B})) |-> ##0 !$isunknown(X); endproperty
  a_known_in_known_out: assert property (p_known_in_known_out);

  // Coverage: all truth-table points observed
  c_00_0: cover property (@(A or B) ##0 (A==0 && B==0 && X==0));
  c_01_1: cover property (@(A or B) ##0 (A==0 && B==1 && X==1));
  c_10_1: cover property (@(A or B) ##0 (A==1 && B==0 && X==1));
  c_11_0: cover property (@(A or B) ##0 (A==1 && B==1 && X==0));

  // Coverage: output toggles in both directions
  c_x_rise: cover property (@(X) $rose(X));
  c_x_fall: cover property (@(X) $fell(X));

endmodule

bind xor_gate xor_gate_sva sva_inst(.A(A), .B(B), .X(X));