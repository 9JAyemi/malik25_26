// SVA checkers and binds for the given adders (purely combinational)

module full_adder_sva(input a, input b, input cin, input sum, input cout);
  // Functional correctness (concise and complete for 1-bit FA)
  a_sum_cout_eq: assert property (@(a or b or cin)
    {cout, sum} == (a + b + cin))
  else $error("full_adder: {cout,sum} != a+b+cin");

  // Outputs must be known when inputs are known
  a_known: assert property (@(a or b or cin)
    (!$isunknown({a,b,cin})) |-> (!$isunknown({sum,cout})))
  else $error("full_adder: X/Z on outputs with known inputs");

  // Full input-space coverage (8 combos)
  c_000: cover property (@(a or b or cin) (a==0 && b==0 && cin==0));
  c_001: cover property (@(a or b or cin) (a==0 && b==0 && cin==1));
  c_010: cover property (@(a or b or cin) (a==0 && b==1 && cin==0));
  c_011: cover property (@(a or b or cin) (a==0 && b==1 && cin==1));
  c_100: cover property (@(a or b or cin) (a==1 && b==0 && cin==0));
  c_101: cover property (@(a or b or cin) (a==1 && b==0 && cin==1));
  c_110: cover property (@(a or b or cin) (a==1 && b==1 && cin==0));
  c_111: cover property (@(a or b or cin) (a==1 && b==1 && cin==1));
endmodule

bind full_adder full_adder_sva fa_sva(.a(a),.b(b),.cin(cin),.sum(sum),.cout(cout));


module four_bit_adder_sva(
  input [3:0] A, input [3:0] B,
  input [3:0] S, input C_out
);
  // Precompute propagate/generate and carries (CLA form) for strong bitwise checks
  wire [3:0] p = A ^ B;
  wire [3:0] g = A & B;
  wire       c1 = g[0];
  wire       c2 = g[1] | (p[1] & g[0]);
  wire       c3 = g[2] | (p[2] & g[1]) | (p[2] & p[1] & g[0]);
  wire       c4 = g[3] | (p[3] & g[2]) | (p[3] & p[2] & g[1]) | (p[3] & p[2] & p[1] & g[0]);

  // Top-level arithmetic equivalence
  a_sum: assert property (@(A or B)
    {C_out, S} == (A + B))
  else $error("four_bit_adder: {C_out,S} != A+B");

  // Bit-accurate ripple/CLA equivalence (checks carry chain without peeking inside)
  a_bits: assert property (@(A or B)
    (S[0] == p[0]) &&
    (S[1] == (p[1] ^ c1)) &&
    (S[2] == (p[2] ^ c2)) &&
    (S[3] == (p[3] ^ c3)) &&
    (C_out == c4))
  else $error("four_bit_adder: bitwise/CLA mismatch");

  // Outputs must be known when inputs are known
  a_known: assert property (@(A or B)
    (!$isunknown({A,B})) |-> (!$isunknown({S,C_out})))
  else $error("four_bit_adder: X/Z on outputs with known inputs");

  // Targeted functional coverage
  // Ripple-through case (all propagates) producing full carry
  c_ripple:   cover property (@(A or B) (A==4'hF && B==4'h1 && S==4'h0 && C_out==1));
  // No-carry trivial case
  c_zero:     cover property (@(A or B) (A==4'h0 && B==4'h0 && S==4'h0 && C_out==0));
  // Max+max overflow
  c_maxmax:   cover property (@(A or B) (A==4'hF && B==4'hF && S==4'hE && C_out==1));
  // Observe both carry-out polarities
  c_co1:      cover property (@(A or B) C_out==1);
  c_co0:      cover property (@(A or B) C_out==0);

  // Per-bit generate/propagate/kill seen at least once
  genvar i;
  generate
    for (i=0;i<4;i++) begin : cov_bits
      c_prop: cover property (@(A or B) (A[i]^B[i])==1);      // propagate
      c_gen:  cover property (@(A or B) (A[i]&B[i])==1);      // generate
      c_kill: cover property (@(A or B) (~A[i] & ~B[i])==1);  // kill
    end
  endgenerate
endmodule

bind four_bit_adder four_bit_adder_sva fba_sva(.A(A),.B(B),.S(S),.C_out(C_out));