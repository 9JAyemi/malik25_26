// SVA for four_bit_adder and full_adder
// Focused, concise checks + meaningful coverage.
// Bind these modules to the DUTs (examples at bottom).

// ---------------- four_bit_adder SVA ----------------
module four_bit_adder_sva (
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic       Cin,
  input  logic [3:0] S,
  input  logic       Cout,
  // internal wires to check
  input  logic [3:0] C,
  input  logic [3:0] G,
  input  logic [3:0] P
);
  // Helper
  function automatic logic carry_next (logic a, logic b, logic cin);
    return (a & b) | (cin & (a ^ b));
  endfunction

  // X-checks: if inputs are known, all outputs/internal wires are known
  assert property (@(*) !$isunknown({A,B,Cin}) |-> !$isunknown({S,Cout,C,G,P}));

  // Top-level arithmetic correctness
  assert property (@(*) {Cout, S} == ({1'b0, A} + {1'b0, B} + Cin));

  // Per-bit sum/carry chain (ripple correctness)
  assert property (@(*) !$isunknown({A[0],B[0],Cin}) |->  S[0] == (A[0]^B[0]^Cin));
  assert property (@(*) !$isunknown({A[0],B[0],Cin}) |->  C[0] == carry_next(A[0],B[0],Cin));

  assert property (@(*) !$isunknown({A[1],B[1],C[0]}) |-> S[1] == (A[1]^B[1]^C[0]));
  assert property (@(*) !$isunknown({A[1],B[1],C[0]}) |-> C[1] == carry_next(A[1],B[1],C[0]));

  assert property (@(*) !$isunknown({A[2],B[2],C[1]}) |-> S[2] == (A[2]^B[2]^C[1]));
  assert property (@(*) !$isunknown({A[2],B[2],C[1]}) |-> C[2] == carry_next(A[2],B[2],C[1]));

  assert property (@(*) !$isunknown({A[3],B[3],C[2]}) |-> S[3] == (A[3]^B[3]^C[2]));
  assert property (@(*) !$isunknown({A[3],B[3],C[2]}) |-> Cout == carry_next(A[3],B[3],C[2]));

  // Internal generate/propagate definitions
  assert property (@(*) G == (A & B));
  assert property (@(*) P == (A ^ B));

  // ------------ Coverage ------------
  // No-carry-out vs carry-out
  cover property (@(*) ({1'b0,A} + {1'b0,B} + Cin) <  16 && Cout == 0);
  cover property (@(*) ({1'b0,A} + {1'b0,B} + Cin) >= 16 && Cout == 1);

  // Corner cases
  cover property (@(*) A==4'h0 && B==4'h0 && Cin==0 && S==4'h0 && Cout==0);
  cover property (@(*) A==4'hF && B==4'hF && Cin==1 && S==4'hF && Cout==1);

  // Full propagate chain (all bits propagate, Cin ripples through)
  cover property (@(*) P==4'hF && Cin==1 && Cout==1);

  // See at least one generate in each bit
  cover property (@(*) G[0]);
  cover property (@(*) G[1]);
  cover property (@(*) G[2]);
  cover property (@(*) G[3]);
endmodule


// ---------------- full_adder SVA ----------------
module full_adder_sva (
  input  logic A,
  input  logic B,
  input  logic Cin,
  input  logic S,
  input  logic Cout
);
  // X-check
  assert property (@(*) !$isunknown({A,B,Cin}) |-> !$isunknown({S,Cout}));

  // Arithmetic correctness (2-bit sum)
  assert property (@(*) {Cout, S} == ({1'b0,A} + {1'b0,B} + Cin));

  // Logical forms (redundant but strong)
  assert property (@(*) S    == (A ^ B ^ Cin));
  assert property (@(*) Cout == ((A & B) | (A & Cin) | (B & Cin)));

  // Coverage: sanity, generate, and propagate-with-carry
  cover property (@(*) A==0 && B==0 && Cin==0 && S==0 && Cout==0);
  cover property (@(*) A==1 && B==1 && Cin==1 && S==1 && Cout==1);
  cover property (@(*) (A & B));                   // generate
  cover property (@(*) (A ^ B) && Cin && Cout);    // propagate a carry
endmodule


// ---------------- Example binds (edit to your env) ----------------
// Bind into the module types so every instance is checked.
// Provide connectivity to internal C/G/P for the 4-bit adder.
//
// bind four_bit_adder four_bit_adder_sva
//   u_four_bit_adder_sva ( .A(A), .B(B), .Cin(Cin), .S(S), .Cout(Cout), .C(C), .G(G), .P(P) );
//
// bind full_adder full_adder_sva
//   u_full_adder_sva ( .A(A), .B(B), .Cin(Cin), .S(S), .Cout(Cout) );