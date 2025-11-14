// SVA for four_bit_adder and full_adder
// Bind these checkers to the DUTs; no TB code required.

bind four_bit_adder four_bit_adder_sva (
  .A(A), .B(B), .Cin(Cin), .S(S), .Cout(Cout)
);

bind full_adder full_adder_sva (
  .a(a), .b(b), .cin(cin), .sum(sum), .cout(cout)
);


// 4-bit adder checker
module four_bit_adder_sva
(
  input logic [3:0] A, B,
  input logic       Cin,
  input logic [3:0] S,
  input logic       Cout
);
  default clocking cb @(*); endclocking

  // Knownness
  assert property (!$isunknown({A,B,Cin})) else $error("Inputs contain X/Z");
  assert property (##0 !$isunknown({S,Cout})) else $error("Outputs contain X/Z");

  // Functional correctness: ripple result equals A+B+Cin
  assert property (1'b1 |-> ##0 {Cout, S} === (A + B + Cin))
    else $error("Adder result mismatch");

  // Compact functional coverage (corner cases + carry behavior)
  cover property (A==4'h0 && B==4'h0 && Cin==1'b0);           // all zeros
  cover property (A==4'hF && B==4'hF && Cin==1'b1);           // max overflow
  cover property (A==4'h0 && B==4'hF && Cin==1'b0);           // pass-through
  cover property (A==4'h5 && B==4'hA && Cin==1'b1);           // full propagate chain
  cover property (Cout==1'b0);
  cover property (Cout==1'b1);
endmodule


// 1-bit full_adder checker (also validates internal stages when bound per instance)
module full_adder_sva
(
  input logic a, b, cin,
  input logic sum, cout
);
  default clocking cb @(*); endclocking

  // Knownness
  assert property (!$isunknown({a,b,cin})) else $error("FA inputs contain X/Z");
  assert property (##0 !$isunknown({sum,cout})) else $error("FA outputs contain X/Z");

  // Functional correctness
  assert property (1'b1 |-> ##0 {cout, sum} === (a + b + cin))
    else $error("Full adder result mismatch");

  // Exhaustive 1-bit input coverage (8 combinations)
  genvar i;
  generate
    for (i=0; i<8; i++) begin : g_cov_all_inputs
      cover property ( {a,b,cin} == i[2:0] );
    end
  endgenerate

  // Cover the three canonical carry classes
  cover property ( (a & b) && cout && (sum == cin) );       // generate
  cover property ( (~a & ~b) && !cout && (sum == cin) );    // kill
  cover property ( (a ^ b) && (cout == cin) );              // propagate
endmodule