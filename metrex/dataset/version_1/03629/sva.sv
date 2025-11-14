// SVA checker for four_bit_adder
module four_bit_adder_sva (input logic clk, rst_n);
  // This module is intended to be bound into four_bit_adder's scope.
  // It assumes visibility of A, B, Cin, S, Cout, and internal C[3:0].

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Derived arithmetic reference
  logic [4:0] sum5;
  assign sum5 = {1'b0, A} + {1'b0, B} + Cin;

  // Knownness: if inputs are known, all derived outputs must be known
  assert property (!$isunknown({A, B, Cin})) |-> !$isunknown({S, Cout, C});

  // End-to-end: 5-bit result must match concatenation of Cout and S
  assert property ({Cout, S} == sum5);

  // Per-bit FA equations and carry chain consistency
  logic [3:0] ci, co;
  assign ci[0] = Cin;
  assign ci[1] = C[0];
  assign ci[2] = C[1];
  assign ci[3] = C[2];

  assign co[0] = C[0];
  assign co[1] = C[1];
  assign co[2] = C[2];
  assign co[3] = Cout;

  genvar i;
  generate
    for (i = 0; i < 4; i++) begin : g_bit_checks
      assert property (S[i] == (A[i] ^ B[i] ^ ci[i]));
      assert property (co[i] == ((A[i] & B[i]) | (ci[i] & (A[i] ^ B[i]))));
    end
  endgenerate

  // Functional coverage (concise but meaningful)
  // Basic zero case
  cover property (A == 4'h0 && B == 4'h0 && !Cin && S == 4'h0 && !Cout);

  // Overflow and no-overflow observed
  cover property (sum5[4] == 1'b0 && Cout == 1'b0);
  cover property (sum5[4] == 1'b1 && Cout == 1'b1);

  // Full propagate chain (A^B=1 for all bits, no generate) with Cin=1 rippling to Cout
  cover property ((A ^ B) == 4'hF && (A & B) == 4'h0 && Cin && Cout);

  // Generate-driven Cout with Cin=0 (at least one bit generates)
  cover property ((A & B) != 4'h0 && !Cin && Cout);

  // Each stage produces a carry at least once
  cover property (C[0]);
  cover property (C[1]);
  cover property (C[2]);
  cover property (Cout);
endmodule

// Example bind (connect an environment clock/reset):
// bind four_bit_adder four_bit_adder_sva u_four_bit_adder_sva(.clk(tb_clk), .rst_n(tb_rst_n));