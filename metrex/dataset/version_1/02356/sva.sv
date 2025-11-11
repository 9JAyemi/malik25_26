// SVA for four_bit_adder
// Checks full 5-bit correctness and basic health; includes concise, meaningful coverage.

module four_bit_adder_sva (
  input logic        clk,
  input logic [3:0]  A,
  input logic [3:0]  B,
  input logic        Cin,
  input logic [3:0]  S,
  input logic        Cout
);
  default clocking cb @(posedge clk); endclocking

  // 5-bit golden sum
  logic [4:0] sum5;
  always_comb sum5 = {1'b0, A} + {1'b0, B} + Cin;

  // Core functional correctness: full 5-bit result must match
  assert property ({Cout, S} == sum5)
    else $error("Adder mismatch: A=%0h B=%0h Cin=%0b => got {Cout,S}=%0h exp=%0h",
                A, B, Cin, {Cout,S}, sum5);

  // Outputs must not be X/Z when inputs are known
  assert property (!$isunknown({A,B,Cin}) |-> !$isunknown({S,Cout}))
    else $error("Unknown on outputs with known inputs: A=%0h B=%0h Cin=%0b S=%0h Cout=%0b",
                A, B, Cin, S, Cout);

  // Basic coverage: hit carry/no-carry and extreme sums
  cover property (Cout == 0);
  cover property (Cout == 1);
  cover property (S == 4'h0);
  cover property (S == 4'hF);

  // Corner cases
  cover property (A == 4'h0 && B == 4'h0 && Cin == 1'b0);          // all zero
  cover property (A == 4'hF && B == 4'hF && Cin == 1'b1);          // max overflow
  cover property (A == 4'hF && B == 4'h0 && Cin == 1'b1);          // full propagate
  cover property (A == 4'h1 && B == 4'h1 && Cin == 1'b0);          // LSB generate

  // Propagate-into-MSB case (carry into bit3 from lower bits with A3^B3=1, Cin=0)
  cover property ( (({1'b0,A[2:0]} + {1'b0,B[2:0]} + Cin)[3]) && (A[3]^B[3]) && !Cin );

  // MSB-generate with no lower carry
  cover property ( (A[3] & B[3]) && !(({1'b0,A[2:0]} + {1'b0,B[2:0]} + Cin)[3]) );

endmodule

// Bind into the DUT (bind by module name)
bind four_bit_adder four_bit_adder_sva sva_i (.*);