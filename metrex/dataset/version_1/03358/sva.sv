// SVA for full_adder and ripple_carry_adder
// Concise, high-quality functional checks, structure checks, and targeted coverage

// ---------------- full_adder SVA ----------------
module full_adder_sva (
  input A,
  input B,
  input C_in,
  input Sum,
  input C_out
);
  default clocking cb @(*); endclocking

  // Functional correctness (2-bit result equals 1-bit add)
  assert property ( {C_out, Sum} == (A + B + C_in) );

  // Outputs are known when inputs are known
  assert property ( !$isunknown({A,B,C_in}) |-> !$isunknown({Sum,C_out}) );

  // Full input-space coverage (all 8 combos)
  cover property ( {A,B,C_in} == 3'b000 );
  cover property ( {A,B,C_in} == 3'b001 );
  cover property ( {A,B,C_in} == 3'b010 );
  cover property ( {A,B,C_in} == 3'b011 );
  cover property ( {A,B,C_in} == 3'b100 );
  cover property ( {A,B,C_in} == 3'b101 );
  cover property ( {A,B,C_in} == 3'b110 );
  cover property ( {A,B,C_in} == 3'b111 );
endmodule

bind full_adder full_adder_sva i_full_adder_sva (.*);


// ---------------- ripple_carry_adder SVA ----------------
module ripple_carry_adder_sva (
  input  [3:0] A,
  input  [3:0] B,
  input        C_in,
  input  [3:0] Sum,
  input        C_out,
  input  [3:0] carry
);
  default clocking cb @(*); endclocking

  // High-level correctness: 5-bit sum matches arithmetic reference
  assert property ( {C_out, Sum} == (A + B + C_in) );

  // Structural carry-chain checks (ripple behavior per stage)
  assert property ( carry[0] == ((A[0] & B[0]) | (C_in   & (A[0] ^ B[0]))) );
  assert property ( carry[1] == ((A[1] & B[1]) | (carry[0] & (A[1] ^ B[1]))) );
  assert property ( carry[2] == ((A[2] & B[2]) | (carry[1] & (A[2] ^ B[2]))) );
  assert property ( C_out    == ((A[3] & B[3]) | (carry[2] & (A[3] ^ B[3]))) );

  // Outputs (and driven internal carries) are known when inputs are known
  assert property ( !$isunknown({A,B,C_in}) |-> !$isunknown({Sum,C_out,carry[2:0]}) );

  // Targeted, meaningful coverage
  // - No overflow
  cover property ( (A + B + C_in) <= 4'hF && !C_out );
  // - Overflow
  cover property ( (A + B + C_in) >  4'hF &&  C_out );
  // - Full propagate chain (all bits propagate and carry ripples through)
  cover property ( ((A ^ B) == 4'hF) && C_in && C_out );
  // - Zero result
  cover property ( {C_out, Sum} == 5'h00 );
endmodule

bind ripple_carry_adder ripple_carry_adder_sva i_rca_sva (.*);