// Here is a bindable SVA checker that exhaustively verifies the CLA’s functionality and internal relations and provides meaningful coverage. Bind it into your DUT (example bind shown at bottom).

module CLA_sva #(parameter bits = 4) (
  input logic clk,
  input logic rst_n
);
  // This checker is bound inside CLA, so it can directly see all DUT signals:
  // operand1, operand2, carryIn, result, carryOut, p, g,
  // bitsP, bitsG, innerP, innerG, resC

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n || $isunknown({operand1, operand2, carryIn}));

  // Golden add check (end-to-end)
  assert property ({carryOut, result} == {1'b0, operand1} + {1'b0, operand2} + carryIn);

  // Top-level relations
  assert property (p == innerP[bits-1]);
  assert property (g == innerG[bits-1]);
  assert property (carryOut == (g | (p & carryIn)));
  assert property (!$isunknown({result, carryOut, p, g}));

  // Base conditions
  assert property (resC[0] == carryIn);
  assert property (innerP[0] == bitsP[0]);
  assert property (innerG[0] == bitsG[0]);

  // Per-bit assertions and coverage
  genvar i;
  generate
    for (i = 0; i < bits; i++) begin : per_bit_checks
      // Bit-level P/G definitions
      assert property (bitsP[i] == (operand1[i] | operand2[i]));
      assert property (bitsG[i] == (operand1[i] & operand2[i]));
      // Sum bit formulation
      assert property (result[i] == (operand1[i] ^ operand2[i] ^ resC[i]));
      // No X/Z on internal nets/outputs when inputs known
      assert property (!$isunknown({bitsP[i], bitsG[i], innerP[i], innerG[i], resC[i], result[i]}));

      // Functional coverage of bit cell classes
      cover property (operand1[i] == 0 && operand2[i] == 0);                 // KILL
      cover property ((operand1[i] ^ operand2[i]) == 1 && bitsG[i] == 0);    // PROP-only
      cover property (operand1[i] == 1 && operand2[i] == 1);                 // GENERATE

      // Coverage of carry into each bit
      cover property (resC[i] == 0);
      cover property (resC[i] == 1);
    end
  endgenerate

  // Chain relations across bits
  genvar j;
  generate
    for (j = 1; j < bits; j++) begin : chain_checks
      assert property (innerG[j] == (bitsG[j] | (bitsP[j] & innerG[j-1])));
      assert property (innerP[j] == (bitsP[j] & innerP[j-1]));
      assert property (resC[j] == (innerG[j-1] | (innerP[j-1] & carryIn)));
    end
  endgenerate

  // Top-level carry behavior coverage
  cover property (carryIn == 0);
  cover property (carryIn == 1);
  cover property (g == 1 && carryOut == 1);                          // block generate causes carry
  cover property (g == 0 && p == 1 && carryIn == 1 && carryOut == 1);// propagate causes carry
  cover property (g == 0 && p == 0 && carryIn == 0 && carryOut == 0);// no carry

  // Extremes / corner patterns
  cover property (operand1 == '0 && operand2 == '0 && carryIn == 0);
  cover property (operand1 == {bits{1'b1}} && operand2 == {bits{1'b1}} && carryIn == 0);
  cover property (operand1 == {bits{1'b1}} && operand2 == '0 && carryIn == 1);
endmodule

// Example bind (in your testbench or a bind file)
// Replace tb_clk/tb_rst_n with your TB clock/reset.
bind CLA CLA_sva #(.bits(bits)) u_CLA_sva (.clk(tb_clk), .rst_n(tb_rst_n));