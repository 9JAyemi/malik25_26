// SVA checker for ripple_carry_adder
module rca_sva (
    input  logic [3:0] A,
    input  logic [3:0] B,
    input  logic [3:0] S,
    input  logic       C,
    input  logic       carry_out,
    input  logic [3:0] carry_in
);

  // Sample whenever any input bit changes; use ##0 to evaluate after combinational settle
  default clocking cb @ (A[0] or A[1] or A[2] or A[3] or B[0] or B[1] or B[2] or B[3]); endclocking

  // End-to-end correctness (5-bit sum)
  assert property (1'b1 |-> ##0 {C,S} == ({1'b0,A} + {1'b0,B}));

  // Bit 0
  assert property (1'b1 |-> ##0 S[0]       == (A[0] ^ B[0]));
  assert property (1'b1 |-> ##0 carry_out  == (A[0] & B[0]));

  // Bit 1
  assert property (1'b1 |-> ##0 S[1]        == (A[1] ^ B[1] ^ carry_out));
  assert property (1'b1 |-> ##0 carry_in[1] == ((A[1] & B[1]) | ((A[1] ^ B[1]) & carry_out)));

  // Bit 2
  assert property (1'b1 |-> ##0 S[2]        == (A[2] ^ B[2] ^ carry_in[1]));
  assert property (1'b1 |-> ##0 carry_in[2] == ((A[2] & B[2]) | ((A[2] ^ B[2]) & carry_in[1])));

  // Bit 3 and final carry
  assert property (1'b1 |-> ##0 S[3] == (A[3] ^ B[3] ^ carry_in[2]));
  assert property (1'b1 |-> ##0 C    == ((A[3] & B[3]) | ((A[3] ^ B[3]) & carry_in[2])));

  // Known-output check for known inputs (guards X/Z propagation)
  assert property (!$isunknown({A,B}) |-> ##0 !$isunknown({S,C,carry_out,carry_in[1],carry_in[2]}));

  // Concise functional coverage
  cover property (##0 (C==0));                         // no final carry
  cover property (##0 (C==1));                         // final carry
  cover property (##0 ({A,B} == {4'h0,4'h0}));         // 0+0
  cover property (##0 ({A,B} == {4'hF,4'hF}));         // max+max
  // Long propagate chain: carry from bit0 ripples through bits 1 and 2 to C
  cover property (##0 (carry_out &&
                       (A[1]^B[1]) && !(A[1]&B[1]) &&
                       (A[2]^B[2]) && !(A[2]&B[2]) &&
                       C));

endmodule

// Bind into DUT to access internal carries
bind ripple_carry_adder rca_sva u_rca_sva (
  .A(A), .B(B), .S(S), .C(C),
  .carry_out(carry_out),
  .carry_in(carry_in)
);