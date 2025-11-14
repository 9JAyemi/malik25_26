module and_gate_sva (
  input logic A,
  input logic B,
  input logic Y,
  input logic not_A,
  input logic not_B,
  input logic or_out,
  input logic nand_out
);

  // Functional equivalence
  assert property (@(*) (Y === (A & B)));

  // Structural checks
  assert property (@(*) (not_A  === ~A));
  assert property (@(*) (not_B  === ~B));
  assert property (@(*) (or_out === (not_A | not_B)));
  assert property (@(*) (nand_out === ~(or_out & or_out)));
  assert property (@(*) (Y === nand_out));

  // No-X propagation when inputs are known
  assert property (@(*) (!$isunknown({A,B})) |-> !$isunknown({not_A,not_B,or_out,nand_out,Y}));

  // Output changes only when an input changes
  assert property (@(*) $changed(Y) |-> ($changed(A) || $changed(B)));

  // Edge sanity: Y edges reflect A&B
  assert property (@(*) $rose(Y) |-> (A && B));
  assert property (@(*) $fell(Y) |-> !(A && B));

  // Truth table coverage
  cover property (@(*) (A==0 && B==0 && Y==0));
  cover property (@(*) (A==0 && B==1 && Y==0));
  cover property (@(*) (A==1 && B==0 && Y==0));
  cover property (@(*) (A==1 && B==1 && Y==1));

  // Output toggle coverage
  cover property (@(*) $rose(Y));
  cover property (@(*) $fell(Y));

endmodule

// Bind into every and_gate instance; internal nets are connected by name
bind and_gate and_gate_sva sva_and_gate (
  .A(A), .B(B), .Y(Y),
  .not_A(not_A), .not_B(not_B),
  .or_out(or_out), .nand_out(nand_out)
);