// SVA for four_bit_adder/full_adder
package four_bit_adder_sva_pkg;
  function automatic logic sum1 (input logic a,b,cin);
    return a ^ b ^ cin;
  endfunction

  function automatic logic cout1 (input logic a,b,cin);
    return (a & b) | ((a ^ b) & cin);
  endfunction

  function automatic logic [4:0] add5 (input logic [3:0] a,b, input logic cin);
    return a + b + cin;
  endfunction
endpackage


// Bind to the 4-bit adder (top)
module four_bit_adder_sva (
  input logic [3:0] A, B,
  input logic       Cin,
  input logic [3:0] S,
  input logic       Cout
);
  import four_bit_adder_sva_pkg::*;
  default clocking cb @ (posedge $global_clock); endclocking

  // Expected bitwise carries and sums
  logic c0, c1, c2, c3;
  assign c0 = cout1(A[0], B[0], Cin);
  assign c1 = cout1(A[1], B[1], c0);
  assign c2 = cout1(A[2], B[2], c1);
  assign c3 = cout1(A[3], B[3], c2);

  logic [4:0] exp;
  assign exp = add5(A, B, Cin);

  // Core functional correctness
  assert property ({Cout, S} == exp);
  assert property (S[0] == sum1(A[0], B[0], Cin));
  assert property (S[1] == sum1(A[1], B[1], c0));
  assert property (S[2] == sum1(A[2], B[2], c1));
  assert property (S[3] == sum1(A[3], B[3], c2));
  assert property (Cout == c3);

  // Carry-lookahead equivalence for Cout
  logic [3:0] p, g;
  assign p = A ^ B;
  assign g = A & B;
  logic exp_cout;
  assign exp_cout = g[3] |
                    (p[3] & g[2]) |
                    (p[3] & p[2] & g[1]) |
                    (p[3] & p[2] & p[1] & g[0]) |
                    (p[3] & p[2] & p[1] & p[0] & Cin);
  assert property (Cout == exp_cout);

  // Concise, meaningful coverage
  cover property (p == 4'b0000);                // no propagate anywhere
  cover property (&p);                          // all propagate
  cover property (&p && Cin && (Cout == Cin));  // full ripple from Cin
  cover property (Cout && !Cin);                // carry-out from generate network
  cover property ({Cout, S} == 5'b0_0000);      // sum zero
  cover property ({Cout, S} == 5'b1_1111);      // max result 31
  // Carry-chain length 0..3
  cover property (!p[0]);
  cover property ( p[0] && !p[1]);
  cover property ( p[0] &&  p[1] && !p[2]);
  cover property ( p[0] &&  p[1] &&  p[2] && !p[3]);
endmodule

bind four_bit_adder four_bit_adder_sva four_bit_adder_sva_i (.*);


// Bind to each 1-bit full_adder slice
module full_adder_sva (
  input logic A, B, Cin,
  input logic S, Cout
);
  import four_bit_adder_sva_pkg::*;
  default clocking cb @ (posedge $global_clock); endclocking

  // Truth-table correctness
  assert property (S    == sum1 (A, B, Cin));
  assert property (Cout == cout1(A, B, Cin));

  // Compact coverage: propagate, generate, kill across Cin=0/1
  cover property (~A & ~B & ~Cin); // kill, Cin=0
  cover property (~A & ~B &  Cin); // kill, Cin=1
  cover property ((A ^ B) & ~Cin); // propagate, Cin=0
  cover property ((A ^ B) &  Cin); // propagate, Cin=1
  cover property (A & B & ~Cin);   // generate, Cin=0
  cover property (A & B &  Cin);   // generate, Cin=1
endmodule

bind full_adder full_adder_sva full_adder_sva_i (.*);