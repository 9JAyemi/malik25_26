// SVA for four_bit_adder and its full_adder sub-block.
// Uses input-change as the sampling event and ##0 to sample after delta-cycle settle.

module four_bit_adder_sva(
  input logic [3:0] A, B,
  input logic       C_in,
  input logic [3:0] S,
  input logic       C_out
);
  logic [3:0] P, G;
  logic c1, c2, c3;

  assign P  = A ^ B;
  assign G  = A & B;
  assign c1 = G[0] | (P[0] & C_in);
  assign c2 = G[1] | (P[1] & c1);
  assign c3 = G[2] | (P[2] & c2);

  // Well-defined outputs whenever inputs are known
  assert property (@(A or B or C_in) !$isunknown({A,B,C_in}) |-> ##0 !$isunknown({S,C_out}));

  // Top-level arithmetic equivalence
  assert property (@(A or B or C_in) !$isunknown({A,B,C_in}) |-> ##0 {C_out,S} == A + B + C_in);

  // Bit-level checks via propagate/generate chain
  assert property (@(A or B or C_in) !$isunknown({A,B,C_in}) |-> ##0 S[0] == (P[0] ^ C_in));
  assert property (@(A or B or C_in) !$isunknown({A,B,C_in}) |-> ##0 S[1] == (P[1] ^ c1));
  assert property (@(A or B or C_in) !$isunknown({A,B,C_in}) |-> ##0 S[2] == (P[2] ^ c2));
  assert property (@(A or B or C_in) !$isunknown({A,B,C_in}) |-> ##0 S[3] == (P[3] ^ c3));
  assert property (@(A or B or C_in) !$isunknown({A,B,C_in}) |-> ##0 C_out == (G[3] | (P[3] & c3)));

  // Focused functional coverage
  cover property (@(A or B or C_in) ##0 !$isunknown({A,B,C_in}) && (C_out==0));
  cover property (@(A or B or C_in) ##0 !$isunknown({A,B,C_in}) && (C_out==1));
  // Full ripple propagate path exercised (all P=1)
  cover property (@(A or B or C_in) ##0 (!$isunknown({A,B,C_in})) && (&P) &&  C_in && (C_out==1));
  cover property (@(A or B or C_in) ##0 (!$isunknown({A,B,C_in})) && (&P) && !C_in && (C_out==0));
  // Generate at each bit at least once
  cover property (@(A or B or C_in) ##0 (!$isunknown({A,B,C_in})) && G[0]);
  cover property (@(A or B or C_in) ##0 (!$isunknown({A,B,C_in})) && G[1]);
  cover property (@(A or B or C_in) ##0 (!$isunknown({A,B,C_in})) && G[2]);
  cover property (@(A or B or C_in) ##0 (!$isunknown({A,B,C_in})) && G[3]);
  // Sum zero with and without overflow
  cover property (@(A or B or C_in) ##0 (!$isunknown({A,B,C_in})) && (S==4'h0) && (C_out==0));
  cover property (@(A or B or C_in) ##0 (!$isunknown({A,B,C_in})) && (S==4'h0) && (C_out==1));
endmodule


module full_adder_sva(
  input logic A, B, C_in,
  input logic S, C_out
);
  // Outputs known when inputs known
  assert property (@(A or B or C_in) !$isunknown({A,B,C_in}) |-> ##0 !$isunknown({S,C_out}));
  // Truth-table equivalence
  assert property (@(A or B or C_in) !$isunknown({A,B,C_in}) |-> ##0 S == (A ^ B ^ C_in));
  assert property (@(A or B or C_in) !$isunknown({A,B,C_in}) |-> ##0 C_out == ((A & B) | (C_in & (A ^ B))));

  // Minimal coverage of propagate/generate/kill and carry out
  cover property (@(A or B or C_in) ##0 (A ^ B) && !C_in && (C_out==0)); // propagate, no carry
  cover property (@(A or B or C_in) ##0 (A ^ B) &&  C_in && (C_out==1)); // propagate, carry
  cover property (@(A or B or C_in) ##0 (A & B) && (C_out==1));          // generate
  cover property (@(A or B or C_in) ##0 !(A|B) && !C_in && (C_out==0));  // kill
endmodule


// Bind these checkers to the DUTs
bind four_bit_adder four_bit_adder_sva u_four_bit_adder_sva(.A(A), .B(B), .C_in(C_in), .S(S), .C_out(C_out));
bind full_adder     full_adder_sva     u_full_adder_sva    (.A(A), .B(B), .C_in(C_in), .S(S), .C_out(C_out));