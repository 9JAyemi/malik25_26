// SVA checkers and binds for four_bit_adder and full_adder.
// Focused, concise, and comprehensive for functionality, connectivity, and X-checking.

module sva_four_bit_adder_chk (
  input  logic [3:0] A, B,
  input  logic       Cin,
  input  logic [3:0] S,
  input  logic       Cout,
  input  logic       c0, c1, c2
);
  event comb_ev;
  always @(*) -> comb_ev;
  default clocking cb @ (comb_ev); endclocking

  // Only evaluate when inputs are known
  // Functional equivalence
  ap_sum_all: assert property (disable iff ($isunknown({A,B,Cin})))
    {Cout,S} == A + B + Cin;

  // Stage-wise sum/carry equations (also checks ripple connections)
  ap_s0:  assert property (disable iff ($isunknown({A,B,Cin}))) S[0] == (A[0]^B[0]^Cin);
  ap_c0:  assert property (disable iff ($isunknown({A,B,Cin}))) c0   == ((A[0]&B[0]) | (A[0]&Cin) | (B[0]&Cin));
  ap_s1:  assert property (disable iff ($isunknown({A,B,Cin}))) S[1] == (A[1]^B[1]^c0);
  ap_c1:  assert property (disable iff ($isunknown({A,B,Cin}))) c1   == ((A[1]&B[1]) | (A[1]&c0)  | (B[1]&c0));
  ap_s2:  assert property (disable iff ($isunknown({A,B,Cin}))) S[2] == (A[2]^B[2]^c1);
  ap_c2:  assert property (disable iff ($isunknown({A,B,Cin}))) c2   == ((A[2]&B[2]) | (A[2]&c1)  | (B[2]&c1));
  ap_s3:  assert property (disable iff ($isunknown({A,B,Cin}))) S[3] == (A[3]^B[3]^c2);
  ap_co:  assert property (disable iff ($isunknown({A,B,Cin}))) Cout == ((A[3]&B[3]) | (A[3]&c2)  | (B[3]&c2));

  // Outputs must be known when inputs are known
  ap_known: assert property ($isunknown({A,B,Cin}) || !$isunknown({S,Cout,c0,c1,c2}));

  // Minimal, meaningful coverage
  //  - zero case
  cp_zero:           cover property ({A,B,Cin} == {4'h0,4'h0,1'b0} && {Cout,S} == 5'h0);
  //  - no-overflow vs overflow
  cp_no_overflow:    cover property (!Cout);
  cp_overflow:       cover property (Cout);
  //  - full carry propagate chain (p=1111, g=0000) with Cin=1
  cp_full_propagate: cover property ((A^B)==4'hF && (A&B)==4'h0 && Cin && Cout);
endmodule

bind four_bit_adder sva_four_bit_adder_chk u_sva_four_bit_adder_chk (
  .A(A), .B(B), .Cin(Cin), .S(S), .Cout(Cout), .c0(c0), .c1(c1), .c2(c2)
);


// Per-cell checker for full_adder (truth table + full input coverage)
module sva_full_adder_chk (
  input logic a, b, cin,
  input logic sum, cout
);
  event comb_ev;
  always @(*) -> comb_ev;
  default clocking cb @ (comb_ev); endclocking

  ap_sum:  assert property (disable iff ($isunknown({a,b,cin}))) sum  == (a^b^cin);
  ap_cout: assert property (disable iff ($isunknown({a,b,cin}))) cout == ((a&b) | (a&cin) | (b&cin));

  // Cover all 8 input combinations
  cp_000: cover property ({a,b,cin} == 3'b000);
  cp_001: cover property ({a,b,cin} == 3'b001);
  cp_010: cover property ({a,b,cin} == 3'b010);
  cp_011: cover property ({a,b,cin} == 3'b011);
  cp_100: cover property ({a,b,cin} == 3'b100);
  cp_101: cover property ({a,b,cin} == 3'b101);
  cp_110: cover property ({a,b,cin} == 3'b110);
  cp_111: cover property ({a,b,cin} == 3'b111);
endmodule

bind full_adder sva_full_adder_chk u_sva_full_adder_chk (
  .a(a), .b(b), .cin(cin), .sum(sum), .cout(cout)
);