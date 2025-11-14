// SVA checker for xor_8bit
module xor_8bit_sva #(parameter WIDTH=8) (
  input logic [WIDTH-1:0] A,
  input logic [WIDTH-1:0] B,
  input logic [WIDTH-1:0] C
);

  // Sample on any change of inputs/outputs (combinational DUT)
  default clocking cb @(A or B or C); endclocking

  // Functional correctness (4-state clean): C must equal A ^ B
  assert property (C === (A ^ B))
    else $error("xor_8bit: C != A ^ B (A=%0h B=%0h C=%0h)", A, B, C);

  // X/Z hygiene: known inputs => known output
  assert property (!$isunknown({A,B}) |-> !$isunknown(C))
    else $error("xor_8bit: Output has X/Z with known inputs (A=%0h B=%0h C=%0h)", A, B, C);

  // If output is X/Z, at least one input must be X/Z
  assert property ($isunknown(C) |-> $isunknown({A,B}))
    else $error("xor_8bit: Spurious X/Z on output (A=%0h B=%0h C=%0h)", A, B, C);

  // Sanity coverage of key functional corners
  cover property (A == '0 && B == '0 && C == '0);                      // all zeros
  cover property (A == B && C == '0);                                   // identical operands
  cover property (A == ~B && C == {WIDTH{1'b1}});                       // bitwise complement
  cover property (A == {WIDTH{1'b1}} && B == '0 && C == {WIDTH{1'b1}}); // max vs zero

  // Per-bit activity and mapping coverage
  genvar i;
  generate for (i = 0; i < WIDTH; i++) begin : bitcov
    // Each output bit toggles both ways at least once
    cover property ($rose(C[i]));
    cover property ($fell(C[i]));

    // Single-bit stimulus maps to same output bit only
    cover property ((A == ('0 | (1'b1 << i)) && B == '0) && C == ('0 | (1'b1 << i)));
    cover property ((B == ('0 | (1'b1 << i)) && A == '0) && C == ('0 | (1'b1 << i)));
  end endgenerate

endmodule

// Example bind (optional):
// bind xor_8bit xor_8bit_sva #(.WIDTH(8)) xor_8bit_sva_i (.A(A), .B(B), .C(C));