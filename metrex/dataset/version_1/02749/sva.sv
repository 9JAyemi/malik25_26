// SVA for simple_adder. Bind this to the DUT.
//
// Checks:
// - Functional correctness (including same-cycle response) for known inputs
// - No spurious C change without A/B change
// - Known output when inputs are known
// Coverage:
// - Overflow and non-overflow cases
// - Key edge cases

module simple_adder_sva (
  input logic [3:0] A,
  input logic [3:0] B,
  input logic [3:0] C
);

  // Correct result with zero-latency when inputs are known
  property p_add_correct;
    @(A or B) !$isunknown({A,B}) |-> ##0 (C == (A + B));
  endproperty
  assert property (p_add_correct);

  // Output must be known when inputs are known
  property p_known_out_when_known_in;
    @(A or B) !$isunknown({A,B}) |-> ##0 !$isunknown(C);
  endproperty
  assert property (p_known_out_when_known_in);

  // No spurious C change unless A or B changed in the same time step
  property p_c_change_requires_in_change;
    @(C) 1 |-> ($changed(A) || $changed(B));
  endproperty
  assert property (p_c_change_requires_in_change);

  // Coverage: non-overflow and overflow occurrences
  cover property (@(A or B) !$isunknown({A,B}) && ((A + B) < 16));
  cover property (@(A or B) !$isunknown({A,B}) && ((A + B) >= 16));

  // Coverage: a few key edge cases including wrap
  cover property (@(A or B) A==4'd0  && B==4'd0  ##0 C==4'd0);
  cover property (@(A or B) A==4'hF && B==4'hF ##0 C==4'hE);
  cover property (@(A or B) A==4'hF && B==4'd1 ##0 C==4'd0);

endmodule

bind simple_adder simple_adder_sva sva_inst (.A(A), .B(B), .C(C));