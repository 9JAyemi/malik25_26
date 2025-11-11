// SVA for binary_adder and full_adder
// Bind modules; no DUT edits required

module binadd_sva #(parameter W=4)
(
  input  logic [W-1:0] A, B, S,
  input  logic         C_out,
  input  logic [W-1:0] sum,
  input  logic [W:1]   carry
);
  default clocking cb @(*); endclocking

  // Functional correctness (5-bit result)
  assert property (!$isunknown({A,B}) |-> {C_out,S} == ({1'b0,A} + {1'b0,B}));

  // Known outputs when inputs are known
  assert property (!$isunknown({A,B}) |-> !$isunknown({S,C_out}));

  // Bit 0
  assert property (!$isunknown({A,B}) |-> carry[1] == (A[0] & B[0]));
  assert property (!$isunknown({A,B}) |-> sum[0]   == (A[0] ^ B[0] ^ 1'b0));

  // Bit 1
  assert property (!$isunknown({A,B}) |-> carry[2] == ((A[1] & B[1]) | ((A[1]^B[1]) & carry[1])));
  assert property (!$isunknown({A,B}) |-> sum[1]   == (A[1] ^ B[1] ^ carry[1]));

  // Bit 2
  assert property (!$isunknown({A,B}) |-> carry[3] == ((A[2] & B[2]) | ((A[2]^B[2]) & carry[2])));
  assert property (!$isunknown({A,B}) |-> sum[2]   == (A[2] ^ B[2] ^ carry[2]));

  // Bit 3 and final carry
  assert property (!$isunknown({A,B}) |-> sum[3]  == (A[3] ^ B[3] ^ carry[3]));
  assert property (!$isunknown({A,B}) |-> C_out   == ((A[3] & B[3]) | ((A[3]^B[3]) & carry[3])));

  // Structural assignment integrity
  assert property (S === sum);

  // Corner-case coverage
  cover property (A==4'h0 && B==4'h0 && C_out==0 && S==4'h0);          // zero + zero
  cover property (A==4'hF && B==4'h1 && C_out==1);                     // full ripple through all stages
  cover property (A==4'h8 && B==4'h8 && C_out==1 && S==4'h0);          // MSB generate
  cover property (A==4'hA && B==4'h5 && C_out==0);                     // mixed case
endmodule

bind binary_adder binadd_sva sva_binadd(
  .A(A), .B(B), .S(S), .C_out(C_out), .sum(sum), .carry(carry)
);

// Per-full_adder correctness and full truth-table coverage
module fa_sva (input logic a,b,c_in, s, c_out);
  default clocking cb @(*); endclocking

  assert property (!$isunknown({a,b,c_in}) |->
                   (s == (a ^ b ^ c_in)) &&
                   (c_out == ((a & b) | (c_in & (a ^ b)))));

  assert property (!$isunknown({a,b,c_in}) |-> !$isunknown({s,c_out}));

  cover property ({a,b,c_in}==3'b000);
  cover property ({a,b,c_in}==3'b001);
  cover property ({a,b,c_in}==3'b010);
  cover property ({a,b,c_in}==3'b011);
  cover property ({a,b,c_in}==3'b100);
  cover property ({a,b,c_in}==3'b101);
  cover property ({a,b,c_in}==3'b110);
  cover property ({a,b,c_in}==3'b111);
endmodule

bind full_adder fa_sva sva_fa(.*);