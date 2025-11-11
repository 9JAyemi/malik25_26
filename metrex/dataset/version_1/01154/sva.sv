// SVA for four_input_and and o21ba
// Concise, high-quality checks and coverage, bindable to DUTs

// Per-gate checker for o21ba
module o21ba_sva (
  input logic A1,
  input logic A2,
  input logic B1_N,
  input logic X
);
  // Functional equivalence (when inputs are known)
  assert property (@(A1 or A2 or B1_N)
                   disable iff ($isunknown({A1,A2,B1_N}))
                   X === (A1 & A2 & ~B1_N));

  // Output must be known whenever inputs are known
  assert property (@(A1 or A2 or B1_N)
                   disable iff ($isunknown({A1,A2,B1_N}))
                   !$isunknown(X));

  // Basic coverage
  cover property (@(A1 or A2 or B1_N) (A1 & A2 & ~B1_N) && (X == 1'b1));
  cover property (@(A1 or A2 or B1_N) !(A1 & A2 & ~B1_N) && (X == 1'b0));
endmodule


// Top-level checker for four_input_and
module four_input_and_sva (
  input logic A1,
  input logic A2,
  input logic B1_N,
  input logic C1,
  input logic X
);
  // Full functional equivalence to canonical form (when inputs are known)
  assert property (@(A1 or A2 or B1_N or C1)
                   disable iff ($isunknown({A1,A2,B1_N,C1}))
                   X === (A1 & A2 & ~B1_N & ~C1));

  // Output must be known whenever inputs are known
  assert property (@(A1 or A2 or B1_N or C1)
                   disable iff ($isunknown({A1,A2,B1_N,C1}))
                   !$isunknown(X));

  // High/low coverage and each single controlling-factor case
  cover property (@(A1 or A2 or B1_N or C1) (A1 & A2 & ~B1_N & ~C1) && (X == 1'b1)); // X=1 case
  cover property (@(A1 or A2 or B1_N or C1) (A1 &  A2 & ~B1_N &  C1) && (X == 1'b0)); // C1 blocks
  cover property (@(A1 or A2 or B1_N or C1) (A1 &  A2 &  B1_N & ~C1) && (X == 1'b0)); // B1_N blocks
  cover property (@(A1 or A2 or B1_N or C1) (!A1 & A2 & ~B1_N & ~C1) && (X == 1'b0)); // A1 blocks
  cover property (@(A1 or A2 or B1_N or C1) (A1 & !A2 & ~B1_N & ~C1) && (X == 1'b0)); // A2 blocks
endmodule


// Bind into DUTs
bind o21ba         o21ba_sva           o21ba_sva_i   (.*);
bind four_input_and four_input_and_sva four_sva_i    (.*);