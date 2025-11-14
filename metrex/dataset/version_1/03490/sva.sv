// SVA checkers for full_adder and four_bit_adder
// Bind these to the DUTs; they use @(*) sampling (no clock required).

// ---------------- full_adder checker ----------------
module full_adder_sva;

  // Functional correctness (disable when inputs are X/Z)
  assert property (disable iff ($isunknown({A,B,Cin}))) @(*)
    (S == (A ^ B ^ Cin));

  assert property (disable iff ($isunknown({A,B,Cin}))) @(*)
    (Cout == ((A & B) | (Cin & (A ^ B))));

  // Internal wire consistency
  assert property (disable iff ($isunknown({A,B,Cin}))) @(*)
    (w1 == (A ^ B));

  assert property (disable iff ($isunknown({A,B,Cin}))) @(*)
    (w2 == (w1 ^ Cin));

  assert property (disable iff ($isunknown({A,B,Cin}))) @(*)
    (S == w2);

  assert property (disable iff ($isunknown({A,B,Cin}))) @(*)
    (w3 == (A & B));

  assert property (disable iff ($isunknown({A,B,Cin}))) @(*)
    (Cout == (w3 | (w1 & Cin)));

  // Generate/propagate/kill identities
  assert property (disable iff ($isunknown({A,B,Cin}))) @(*)
    ((A & B) |-> (Cout == 1'b1));

  assert property (disable iff ($isunknown({A,B,Cin}))) @(*)
    ((~A & ~B) |-> (Cout == 1'b0));

  assert property (disable iff ($isunknown({A,B,Cin}))) @(*)
    ((A ^ B) |-> (Cout == Cin));

  // Coverage: all 8 input combinations
  cover property (@(*)) ({A,B,Cin} == 3'b000);
  cover property (@(*)) ({A,B,Cin} == 3'b001);
  cover property (@(*)) ({A,B,Cin} == 3'b010);
  cover property (@(*)) ({A,B,Cin} == 3'b011);
  cover property (@(*)) ({A,B,Cin} == 3'b100);
  cover property (@(*)) ({A,B,Cin} == 3'b101);
  cover property (@(*)) ({A,B,Cin} == 3'b110);
  cover property (@(*)) ({A,B,Cin} == 3'b111);

endmodule

bind full_adder full_adder_sva fa_chk();

// ---------------- four_bit_adder checker ----------------
module four_bit_adder_sva;

  // Sum/carry correctness for entire adder
  assert property (disable iff ($isunknown({A,B,Cin}))) @(*)
    ({Cout, S} == (A + B + Cin));

  // Stage-level carry and sum relationships
  assert property (disable iff ($isunknown({A,B,Cin}))) @(*)
    (c1 == ((A[0] & B[0]) | (Cin & (A[0] ^ B[0]))));
  assert property (disable iff ($isunknown({A,B,Cin}))) @(*)
    (c2 == ((A[1] & B[1]) | (c1  & (A[1] ^ B[1]))));
  assert property (disable iff ($isunknown({A,B,Cin}))) @(*)
    (c3 == ((A[2] & B[2]) | (c2  & (A[2] ^ B[2]))));
  assert property (disable iff ($isunknown({A,B,Cin}))) @(*)
    (Cout == ((A[3] & B[3]) | (c3  & (A[3] ^ B[3]))));

  assert property (disable iff ($isunknown({A,B,Cin}))) @(*)
    (S[0] == (A[0] ^ B[0] ^ Cin));
  assert property (disable iff ($isunknown({A,B,Cin}))) @(*)
    (S[1] == (A[1] ^ B[1] ^ c1));
  assert property (disable iff ($isunknown({A,B,Cin}))) @(*)
    (S[2] == (A[2] ^ B[2] ^ c2));
  assert property (disable iff ($isunknown({A,B,Cin}))) @(*)
    (S[3] == (A[3] ^ B[3] ^ c3));

  // Propagate/generate/kill identities per most-significant stage
  assert property (disable iff ($isunknown({A,B,Cin}))) @(*)
    ((A[3] & B[3]) |-> (Cout == 1'b1));
  assert property (disable iff ($isunknown({A,B,Cin}))) @(*)
    ((~A[3] & ~B[3]) |-> (Cout == 1'b0));
  assert property (disable iff ($isunknown({A,B,Cin}))) @(*)
    ((A[3] ^ B[3]) |-> (Cout == c3));

  // Functional coverage (key scenarios)
  // No overflow and overflow
  cover property (@(*)) (Cout == 1'b0);
  cover property (@(*)) (Cout == 1'b1);

  // Full propagate chain (all bits propagate, Cin ripples through)
  cover property (@(*))
    ((A ^ B) == 4'hF && (A & B) == 4'h0 && Cin && S == 4'h0 && Cout);

  // Add zero
  cover property (@(*))
    (B == 4'h0 && !Cin && S == A && !Cout);

  // Max + Max + 1 => overflow with all-one sum
  cover property (@(*))
    (A == 4'hF && B == 4'hF && Cin && S == 4'hF && Cout);

endmodule

bind four_bit_adder four_bit_adder_sva fba_chk();