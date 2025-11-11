// SVA for full_adder_1bit and nand_adder_4bit
// Concise, functional correctness, internal connectivity, X-checks, and key coverage.

module sva_full_adder_1bit (
  input sum, carry, a, b, c,
  input w1, w2, w3
);
  default clocking cb @(*); endclocking

  // No X on outputs when inputs are 0/1
  assert property ( !$isunknown({a,b,c}) |-> !$isunknown({sum,carry,w1,w2,w3}) );

  // Gate connectivity (matches intended NAND logic)
  assert property ( !$isunknown({a,b,c}) |-> w1 == ~(a & b & c) );
  assert property ( !$isunknown({a,b,c}) |-> w2 == ~(w1 & c & b) );
  assert property ( !$isunknown({a,b,c}) |-> w3 == ~(w1 & c & a) );
  assert property ( !$isunknown({a,b,c}) |-> sum == ~(w2 & w3 & c) );
  assert property ( !$isunknown({a,b,c}) |-> carry == ~(w1 & c & a) );

  // Functional correctness (1-bit full adder)
  assert property ( !$isunknown({a,b,c}) |-> sum   == (a ^ b ^ c) );
  assert property ( !$isunknown({a,b,c}) |-> carry == ((a & b) | (a & c) | (b & c)) );

  // Coverage: all 8 input combinations
  genvar i;
  generate
    for (i=0; i<8; i++) begin : cov_fa_inputs
      cover property ( {a,b,c} == i[2:0] );
    end
  endgenerate

  // Coverage: output activity
  cover property ( !$isunknown({a,b,c,sum})   && $changed(sum) );
  cover property ( !$isunknown({a,b,c,carry}) && $changed(carry) );
endmodule


module sva_nand_adder_4bit (
  input [3:0] S, A, B,
  input C_out, C_in,
  input c0, c1, c2, c3,
  input s0, s1, s2, s3
);
  default clocking cb @(*); endclocking

  // No X on outputs when inputs are 0/1
  assert property ( !$isunknown({A,B,C_in}) |-> !$isunknown({S,C_out,c0,c1,c2,c3,s0,s1,s2,s3}) );

  // Vector wiring correctness
  assert property ( S == {s3,s2,s1,s0} );
  assert property ( C_out == c3 );

  // Per-bit functional correctness of ripple chain
  assert property ( !$isunknown({A[0],B[0],C_in}) |-> s0 == (A[0]^B[0]^C_in) );
  assert property ( !$isunknown({A[0],B[0],C_in}) |-> c0 == ((A[0]&B[0])|(A[0]&C_in)|(B[0]&C_in)) );

  assert property ( !$isunknown({A[1],B[1],c0}) |-> s1 == (A[1]^B[1]^c0) );
  assert property ( !$isunknown({A[1],B[1],c0}) |-> c1 == ((A[1]&B[1])|(A[1]&c0)|(B[1]&c0)) );

  assert property ( !$isunknown({A[2],B[2],c1}) |-> s2 == (A[2]^B[2]^c1) );
  assert property ( !$isunknown({A[2],B[2],c1}) |-> c2 == ((A[2]&B[2])|(A[2]&c1)|(B[2]&c1)) );

  assert property ( !$isunknown({A[3],B[3],c2}) |-> s3 == (A[3]^B[3]^c2) );
  assert property ( !$isunknown({A[3],B[3],c2}) |-> c3 == ((A[3]&B[3])|(A[3]&c2)|(B[3]&c2)) );

  // End-to-end correctness (5-bit sum)
  assert property ( !$isunknown({A,B,C_in}) |-> {C_out,S} == ({1'b0,A} + {1'b0,B} + C_in) );

  // Key coverage: extremes, propagate-through, and carry activity
  cover property ( A==4'h0 && B==4'h0 && C_in==1'b0 && {C_out,S}==5'd0 );
  cover property ( A==4'hF && B==4'hF && C_in==1'b1 && {C_out,S}==5'd31 );

  // Full propagate chain: no generate, all propagate, carry-in transfers to out
  cover property ( ( (A^B)==4'hF ) && ( (A&B)==4'h0 ) && (C_in==1'b1) && (C_out==1'b1) );

  // Carry node activity
  cover property ( !$isunknown({A,B,C_in,c0}) && $changed(c0) );
  cover property ( !$isunknown({A,B,C_in,c1}) && $changed(c1) );
  cover property ( !$isunknown({A,B,C_in,c2}) && $changed(c2) );
  cover property ( !$isunknown({A,B,C_in,c3}) && $changed(c3) );
endmodule


// Bind SVA modules to DUTs (captures internal nets/wires)
bind full_adder_1bit sva_full_adder_1bit fa_sva (
  .sum(sum), .carry(carry), .a(a), .b(b), .c(c),
  .w1(w1), .w2(w2), .w3(w3)
);

bind nand_adder_4bit sva_nand_adder_4bit na4_sva (
  .S(S), .C_out(C_out), .A(A), .B(B), .C_in(C_in),
  .c0(c0), .c1(c1), .c2(c2), .c3(c3),
  .s0(s0), .s1(s1), .s2(s2), .s3(s3)
);