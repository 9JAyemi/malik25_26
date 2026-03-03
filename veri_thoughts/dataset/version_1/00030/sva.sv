// SVA for four_bit_adder
// Bind this checker to the DUT; drive clk from your TB (any free-running clock).
// Focuses on functional correctness and key internal wire consistency, plus compact coverage.

module four_bit_adder_sva
(
  input logic        clk,
  // DUT ports
  input logic [3:0]  A,
  input logic [3:0]  B,
  input logic        CI,
  input logic [3:0]  SUM,
  input logic        COUT,
  // DUT internal nets (for structural checks)
  input logic [3:0]  a_xor_b,
  input logic [3:0]  a_xor_b_xor_ci,
  input logic [3:0]  a_and_b,
  input logic [3:0]  a_and_b_and_ci,
  input logic [3:0]  a_or_b,
  input logic [3:0]  a_or_b_or_ci,
  input logic        a_xor_b_xor_ci_xor_cout
);
  default clocking cb @(posedge clk); endclocking

  // Functional correctness (golden arithmetic)
  assert property ({COUT, SUM} == A + B + CI)
    else $error("Adder mismatch: A=%0h B=%0h CI=%0b -> SUM=%0h COUT=%0b, exp=%0h",
                A, B, CI, SUM, COUT, (A + B + CI));

  // X-propagation sanity: known inputs imply known outputs
  assert property (!$isunknown({A,B,CI}) |-> !$isunknown({SUM,COUT}))
    else $error("X/Z on outputs with known inputs: A=%0h B=%0h CI=%0b SUM=%0h COUT=%0b",
                A, B, CI, SUM, COUT);

  // Structural conformance of internal nets to their intended boolean functions
  assert property (a_xor_b           == (A ^  B))
    else $error("a_xor_b wrong: A=%0h B=%0h a_xor_b=%0h", A, B, a_xor_b);

  assert property (a_xor_b_xor_ci    == (a_xor_b ^  {4{CI}}))
    else $error("a_xor_b_xor_ci wrong: a_xor_b=%0h CI=%0b a_xor_b_xor_ci=%0h",
                a_xor_b, CI, a_xor_b_xor_ci);

  assert property (a_and_b           == (A &  B))
    else $error("a_and_b wrong: A=%0h B=%0h a_and_b=%0h", A, B, a_and_b);

  assert property (a_and_b_and_ci    == (a_and_b & {4{CI}}))
    else $error("a_and_b_and_ci wrong: a_and_b=%0h CI=%0b a_and_b_and_ci=%0h",
                a_and_b, CI, a_and_b_and_ci);

  assert property (a_or_b            == (A |  B))
    else $error("a_or_b wrong: A=%0h B=%0h a_or_b=%0h", A, B, a_or_b);

  assert property (a_or_b_or_ci      == (a_or_b | {4{CI}}))
    else $error("a_or_b_or_ci wrong: a_or_b=%0h CI=%0b a_or_b_or_ci=%0h",
                a_or_b, CI, a_or_b_or_ci);

  assert property (a_xor_b_xor_ci_xor_cout == (a_xor_b_xor_ci[3] ^ a_and_b_and_ci[3]))
    else $error("cout int wrong: sum3=%0b and3&ci=%0b cout_int=%0b",
                a_xor_b_xor_ci[3], a_and_b_and_ci[3], a_xor_b_xor_ci_xor_cout);

  // Output port mapping correctness
  assert property (SUM  == a_xor_b_xor_ci)
    else $error("SUM port wrong: SUM=%0h a_xor_b_xor_ci=%0h", SUM, a_xor_b_xor_ci);

  assert property (COUT == a_xor_b_xor_ci_xor_cout)
    else $error("COUT port wrong: COUT=%0b int=%0b", COUT, a_xor_b_xor_ci_xor_cout);

  // Compact but strong coverage
  // 1) Cover all 17 possible result values {COUT,SUM} = 0..16
  genvar s;
  generate
    for (s = 0; s <= 16; s++) begin : C_ALL_RESULTS
      localparam [4:0] SV = s[4:0];
      cover property ({COUT, SUM} == SV);
    end
  endgenerate

  // 2) Key corner cases
  cover property (A==4'h0 && B==4'h0 && CI==1'b0 && SUM==4'h0 && COUT==1'b0);
  cover property (A==4'hF && B==4'hF && CI==1'b1 && COUT==1'b1);
  cover property (CI==1'b0);
  cover property (CI==1'b1);
  cover property (COUT==1'b0);
  cover property (COUT==1'b1);

endmodule

// Bind into the DUT. Connect clk from your testbench.
bind four_bit_adder four_bit_adder_sva u_four_bit_adder_sva (
  .clk(clk),                 // provide a TB clock
  .A(A),
  .B(B),
  .CI(CI),
  .SUM(SUM),
  .COUT(COUT),
  .a_xor_b(a_xor_b),
  .a_xor_b_xor_ci(a_xor_b_xor_ci),
  .a_and_b(a_and_b),
  .a_and_b_and_ci(a_and_b_and_ci),
  .a_or_b(a_or_b),
  .a_or_b_or_ci(a_or_b_or_ci),
  .a_xor_b_xor_ci_xor_cout(a_xor_b_xor_ci_xor_cout)
);