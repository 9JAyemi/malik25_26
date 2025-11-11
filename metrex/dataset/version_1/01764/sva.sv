// SVA for and_gate. Bind this to the DUT.
// Focused, high-quality checks and concise full functional coverage.

module and_gate_sva (
  input logic A,
  input logic B,
  input logic C,
  input logic Y
);

  // Sample on any activity of inputs or output
  default clocking cb @(A or B or C or Y); endclocking

  // Functional equivalence when inputs are known
  assert property (disable iff ($isunknown({A,B,C})) (Y === (A & B & C)))
    else $error("and_gate: Y != A&B&C with known inputs");

  // No X on Y when inputs are known
  assert property ((!$isunknown({A,B,C})) |-> !$isunknown(Y))
    else $error("and_gate: Y is X/Z while inputs are known");

  // Output must not change unless inputs change
  assert property ($stable({A,B,C}) |-> $stable(Y))
    else $error("and_gate: Y changed without input change");

  // Edge correlation
  assert property ($rose(Y) |-> (A && B && C))
    else $error("and_gate: Y rose without all inputs high");
  assert property ($fell(Y) |-> (!A || !B || !C))
    else $error("and_gate: Y fell while all inputs stayed high");

  // Full functional coverage: all input combinations with expected Y
  cover property (({A,B,C}==3'b000) && (Y==1'b0));
  cover property (({A,B,C}==3'b001) && (Y==1'b0));
  cover property (({A,B,C}==3'b010) && (Y==1'b0));
  cover property (({A,B,C}==3'b011) && (Y==1'b0));
  cover property (({A,B,C}==3'b100) && (Y==1'b0));
  cover property (({A,B,C}==3'b101) && (Y==1'b0));
  cover property (({A,B,C}==3'b110) && (Y==1'b0));
  cover property (({A,B,C}==3'b111) && (Y==1'b1));

  // Output toggle coverage
  cover property ($rose(Y));
  cover property ($fell(Y));

endmodule

// Bind into the DUT
bind and_gate and_gate_sva u_and_gate_sva (.A(A), .B(B), .C(C), .Y(Y));