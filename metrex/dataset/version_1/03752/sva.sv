// SVA for adder4 and full_adder. Bind these modules to the DUTs.

module adder4_sva (
  input  logic [3:0] A, B,
  input  logic       Cin,
  input  logic [3:0] S,
  input  logic       Cout,
  input  logic [3:0] sum,
  input  logic [3:1] carry
);
  // Disable checks on unknown inputs
  default disable iff ($isunknown({A,B,Cin}));

  // Golden functionality: 5-bit result equals A+B+Cin (sample after settle)
  assert property (@(A or B or Cin) ##0 {Cout,S} == A + B + Cin);

  // Connectivity: S mirrors internal sum bus
  assert property (@(A or B or Cin) ##0 S == sum);

  // Bit-level sum/carry equations and carry chain
  // bit 0
  assert property (@(A or B or Cin) ##0 sum[0]   == (A[0] ^ B[0] ^ Cin));
  assert property (@(A or B or Cin) ##0 carry[1] == (A[0] & B[0]) | (Cin & (A[0] ^ B[0])));
  // bit 1
  assert property (@(A or B or Cin) ##0 sum[1]   == (A[1] ^ B[1] ^ carry[1]));
  assert property (@(A or B or Cin) ##0 carry[2] == (A[1] & B[1]) | (carry[1] & (A[1] ^ B[1])));
  // bit 2
  assert property (@(A or B or Cin) ##0 sum[2]   == (A[2] ^ B[2] ^ carry[2]));
  assert property (@(A or B or Cin) ##0 carry[3] == (A[2] & B[2]) | (carry[2] & (A[2] ^ B[2])));
  // bit 3
  assert property (@(A or B or Cin) ##0 sum[3]   == (A[3] ^ B[3] ^ carry[3]));
  assert property (@(A or B or Cin) ##0 Cout     == (A[3] & B[3]) | (carry[3] & (A[3] ^ B[3])));

  // No X/Z on outputs when inputs are known
  assert property (@(A or B or Cin) ##0 ! $isunknown({S,Cout,sum,carry}));

  // Concise but meaningful functional coverage
  // Full propagate chain with Cin rippling through all bits
  cover property (@(A or B or Cin) (&(A ^ B) && Cin) ##0 (Cout && (S == 4'h0)));
  // MSB generate (independent of incoming carry)
  cover property (@(A or B or Cin) (A[3] & B[3]) ##0 (Cout));
  // Simple zero result
  cover property (@(A or B or Cin) (A==4'h0 && B==4'h0 && !Cin) ##0 (S==4'h0 && !Cout));
  // Max result 0x1F
  cover property (@(A or B or Cin) (A==4'hF && B==4'hF && Cin) ##0 ({Cout,S}==5'h1F));
  // Signed overflow occurrence (carry into MSB xor carry out)
  cover property (@(A or B or Cin) ##0 (carry[3] ^ Cout));
endmodule

bind adder4 adder4_sva adder4_sva_i (.*);


// SVA for 1-bit full_adder
module full_adder_sva (
  input logic A, B, Cin,
  input logic S, Cout
);
  default disable iff ($isunknown({A,B,Cin}));

  // Golden functionality and gate-level identities
  assert property (@(A or B or Cin) ##0 {Cout,S} == A + B + Cin);
  assert property (@(A or B or Cin) ##0 S        == (A ^ B ^ Cin));
  assert property (@(A or B or Cin) ##0 Cout     == (A & B) | (Cin & (A ^ B)));

  // Derived carry properties (propagate/generate/kill)
  assert property (@(A or B or Cin) (A ^ B)  |-> ##0 (Cout == Cin));
  assert property (@(A or B or Cin) !(A ^ B) |-> ##0 (Cout == (A & B)));

  // No X/Z on outputs when inputs are known
  assert property (@(A or B or Cin) ##0 ! $isunknown({S,Cout}));

  // Coverage: exercise generate, propagate, kill classes
  cover property (@(A or B or Cin) (A & B)         ##0 (Cout && !S));     // generate
  cover property (@(A or B or Cin) ((A ^ B) && Cin)##0 (Cout));           // propagate with carry-through
  cover property (@(A or B or Cin) (!A && !B)      ##0 (!Cout && (S==Cin))); // kill
endmodule

bind full_adder full_adder_sva full_adder_sva_i (.*);