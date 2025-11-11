// SVA checker for left_rotation: o must be i rotated left by n (0..31)
module left_rotation_sva (
  input logic [31:0] i,
  input logic [4:0]  n,
  input logic [31:0] o
);

  // Reference rotate-left using a safe variable part-select
  function automatic logic [31:0] rotl32 (input logic [31:0] x, input logic [4:0] s);
    return {x,x}[31+s -: 32];
  endfunction

  // Helper
  function automatic bit known_inputs();
    return !$isunknown({i,n});
  endfunction

  // n is within range when known (guards ill-formed shifts/selections)
  assert property (@(n) !$isunknown(n) |-> (n < 32))
    else $error("left_rotation: n out of range (n=%0d)", n);

  // Output has no X/Z when inputs are known
  assert property (@(i or n or o) known_inputs() |-> !$isunknown(o))
    else $error("left_rotation: o has X/Z with known inputs, i=%h n=%0d o=%h", i, n, o);

  // Functional equivalence to rotate-left
  assert property (@(i or n or o) known_inputs() |-> (o == rotl32(i,n)))
    else $error("left_rotation: functional mismatch, i=%h n=%0d o=%h exp=%h",
                i, n, o, rotl32(i,n));

  // Inverse consistency: rotating o right by n recovers i (for n!=0)
  assert property (@(i or n or o) (known_inputs() && (n != 0)) |-> ({o,o}[63-n -: 32] == i))
    else $error("left_rotation: inverse check failed, i=%h n=%0d o=%h", i, n, o);

  // Bit-count is preserved by rotation (when all known)
  assert property (@(i or n or o) known_inputs() |-> ($countones(o) == $countones(i)))
    else $error("left_rotation: popcount not preserved, i=%h o=%h", i, o);

  // Coverage: hit all shift amounts 0..31 and key corner cases
  genvar s;
  generate
    for (s = 0; s < 32; s++) begin : COV_S
      cover property (@(n) (!$isunknown(n) && n == s));
    end
  endgenerate

  cover property (@(i or n) (!$isunknown({i,n}) && n == 0 && o == i));
  cover property (@(i or n) (!$isunknown({i,n}) && n == 1 && o == rotl32(i,1)));
  cover property (@(i or n) (!$isunknown({i,n}) && n == 31 && o == rotl32(i,31)));

endmodule

// Bind into the DUT (example):
// bind left_rotation left_rotation_sva u_left_rotation_sva(.i(i), .n(n), .o(o));