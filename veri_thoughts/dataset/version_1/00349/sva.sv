// SVA for xor3. Bind this to the DUT.
// Focuses on correctness, X/Z cleanliness, glitch-freedom, and compact coverage.
module xor3_sva (
  input logic a, b, c,
  input logic y,
  input logic ab_xor,
  input logic abc_xor
);

  // Functional correctness (settled same-timestep)
  assert property (@(a or b or c) 1'b1 |-> ##0 (y == (a ^ b ^ c)));

  // Internal wiring consistency (after settle)
  assert property (@(a or b or c) 1'b1 |-> ##0 (ab_xor == (a ^ b)));
  assert property (@(a or b or c) 1'b1 |-> ##0 (abc_xor == (ab_xor ^ c)));
  assert property (@(a or b or c) 1'b1 |-> ##0 (y == abc_xor));

  // No X/Z on any observable signal after settle
  assert property (@(a or b or c or y) 1'b1 |-> ##0 (!$isunknown({a,b,c,y,ab_xor,abc_xor})));

  // Glitch-free: y must not change unless at least one input changed
  assert property (@(y) $changed(y) |-> !$stable({a,b,c}));

  // Coverage: all 8 input combos with expected y
  cover property (@(a or b or c) ##0 ({a,b,c,y} == 4'b0000));
  cover property (@(a or b or c) ##0 ({a,b,c,y} == 4'b0011));
  cover property (@(a or b or c) ##0 ({a,b,c,y} == 4'b0101));
  cover property (@(a or b or c) ##0 ({a,b,c,y} == 4'b0110));
  cover property (@(a or b or c) ##0 ({a,b,c,y} == 4'b1001));
  cover property (@(a or b or c) ##0 ({a,b,c,y} == 4'b1010));
  cover property (@(a or b or c) ##0 ({a,b,c,y} == 4'b1100));
  cover property (@(a or b or c) ##0 ({a,b,c,y} == 4'b1111));

  // Coverage: single-input toggle causes y to toggle (after settle)
  cover property (@(a or b or c) $changed(a) && $stable(b) && $stable(c) ##0 $changed(y));
  cover property (@(a or b or c) $changed(b) && $stable(a) && $stable(c) ##0 $changed(y));
  cover property (@(a or b or c) $changed(c) && $stable(a) && $stable(b) ##0 $changed(y));

endmodule

bind xor3 xor3_sva sva (.*);