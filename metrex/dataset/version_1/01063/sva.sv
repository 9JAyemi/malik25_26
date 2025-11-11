// SVA checker for my_module
module my_module_sva (
  input logic A1,
  input logic A2,
  input logic B1_N,
  input logic X
);

  // Functional equivalence (4-state)
  assert property (@(*) X === ((A1 & A2) | ~B1_N))
    else $error("X != (A1&A2)|~B1_N");

  // Knownness: when all inputs are known, X must be known
  assert property (@(*) (!$isunknown({A1,A2,B1_N})) |-> !$isunknown(X))
    else $error("Known inputs produced unknown X");

  // Dominance: B1_N low forces X high (even if A1/A2 are X/Z)
  assert property (@(*) (B1_N === 1'b0) |-> (X === 1'b1))
    else $error("B1_N==0 must force X==1");

  // When B1_N is high and A1/A2 are known, X == A1&A2 and is known
  assert property (@(*) (B1_N === 1'b1 && !$isunknown({A1,A2})) |-> (X === (A1 & A2) && !$isunknown(X)))
    else $error("B1_N==1: X must equal A1&A2 and be known");

  // Optional edge-specific checks (same-delta response)
  assert property (@(*) $fell(B1_N) |-> ##0 (X === 1'b1))
    else $error("On B1_N fall, X must be 1 immediately");
  assert property (@(*) ($rose(B1_N) && !$isunknown({A1,A2})) |-> ##0 (X === (A1 & A2)))
    else $error("On B1_N rise, X must equal A1&A2 immediately");

  // Functional coverage: all 8 input combinations with expected X
  cover property (@(*) {A1,A2,B1_N,X} === 4'b0001);
  cover property (@(*) {A1,A2,B1_N,X} === 4'b0101);
  cover property (@(*) {A1,A2,B1_N,X} === 4'b1001);
  cover property (@(*) {A1,A2,B1_N,X} === 4'b1101);
  cover property (@(*) {A1,A2,B1_N,X} === 4'b0010);
  cover property (@(*) {A1,A2,B1_N,X} === 4'b0110);
  cover property (@(*) {A1,A2,B1_N,X} === 4'b1010);
  cover property (@(*) {A1,A2,B1_N,X} === 4'b1111);

  // Toggle coverage on inputs
  cover property (@(*) $rose(A1));  cover property (@(*) $fell(A1));
  cover property (@(*) $rose(A2));  cover property (@(*) $fell(A2));
  cover property (@(*) $rose(B1_N)); cover property (@(*) $fell(B1_N));

endmodule

// Bind into the DUT
bind my_module my_module_sva u_my_module_sva (
  .A1   (A1),
  .A2   (A2),
  .B1_N (B1_N),
  .X    (X)
);