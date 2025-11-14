// SVA checker for custom_or; bind this to the DUT.
// Focused, complete checks and concise coverage.

module custom_or_sva (
  input logic a, b, c,
  input logic x,
  input logic ab, abc
);

  // Functional equivalence (4-state correct)
  assert property (@(a or b or c or ab or abc or x) ab  === (a | b));
  assert property (@(a or b or c or ab or abc or x) abc === (ab | c));
  assert property (@(a or b or c or ab or abc or x) x   === (a | b | c));

  // If inputs are known, output must be known
  assert property (@(a or b or c) !$isunknown({a,b,c}) |-> !$isunknown(x));

  // Full input-space coverage with expected x
  cover property (@(a or b or c or x) {a,b,c,x} == 4'b0000);
  cover property (@(a or b or c or x) {a,b,c,x} == 4'b0011);
  cover property (@(a or b or c or x) {a,b,c,x} == 4'b0101);
  cover property (@(a or b or c or x) {a,b,c,x} == 4'b0111);
  cover property (@(a or b or c or x) {a,b,c,x} == 4'b1001);
  cover property (@(a or b or c or x) {a,b,c,x} == 4'b1011);
  cover property (@(a or b or c or x) {a,b,c,x} == 4'b1101);
  cover property (@(a or b or c or x) {a,b,c,x} == 4'b1111);

endmodule

// Bind into the DUT (accessing internal nets ab, abc)
bind custom_or custom_or_sva sva (
  .a(a), .b(b), .c(c), .x(x),
  .ab(ab), .abc(abc)
);