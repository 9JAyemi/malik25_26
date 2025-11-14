// SVA for binary_adder (bindable, concise, high-signal-quality checks)

module binary_adder_sva(
  input  [3:0] A,
  input  [3:0] B,
  input  [3:0] S,
  input        C
);

  // Functional correctness: 5-bit sum equals {C,S}
  property p_correct_sum;
    @(A or B or S or C) ({C,S} == ({1'b0,A} + {1'b0,B}));
  endproperty
  assert property (p_correct_sum);

  // Outputs never X/Z when observed
  property p_outputs_known;
    @(A or B or S or C) !$isunknown({S,C});
  endproperty
  assert property (p_outputs_known);

  // Basic functional coverage
  cover property (@(A or B) (({1'b0,A}+{1'b0,B}) < 16)  && (C == 1'b0)); // no carry
  cover property (@(A or B) (({1'b0,A}+{1'b0,B}) >= 16) && (C == 1'b1)); // with carry
  cover property (@(A or B) (A==4'h0 && B==4'h0 && {C,S}==5'h00));
  cover property (@(A or B) (A==4'hF && B==4'hF && {C,S}==5'h1E));
  cover property (@(A or B) (A==4'hF && B==4'h1 && {C,S}==5'h10)); // wrap boundary

endmodule

bind binary_adder binary_adder_sva sva_i(.A(A), .B(B), .S(S), .C(C));