// SVA for and_gate: concise, high-quality checks and coverage
// Bind this module to the DUT to verify behavior without modifying RTL.

module and_gate_sva (
  input logic A,
  input logic B,
  input logic Y
);

  // Functional correctness (4-state accurate). Zero-delay consistency on input changes.
  property p_and_func;
    @(A or B) 1'b1 |-> ##0 (Y === (A & B));
  endproperty
  assert property (p_and_func);

  // Output edges must be logically justified by inputs.
  assert property (@(posedge Y)  A && B);
  assert property (@(negedge Y) !(A && B));

  // If inputs are known, output must be known in the same delta.
  assert property (@(A or B) (!$isunknown({A,B})) |-> ##0 (!$isunknown(Y)));

  // Functional coverage: all input combinations with correct Y.
  cover property (@(A or B) (A==0 && B==0 && Y==0));
  cover property (@(A or B) (A==0 && B==1 && Y==0));
  cover property (@(A or B) (A==1 && B==0 && Y==0));
  cover property (@(A or B) (A==1 && B==1 && Y==1));

  // Edge coverage: observe both output transitions under correct conditions.
  cover property (@(posedge Y)  A && B);
  cover property (@(negedge Y) !(A && B));

endmodule

// Bind to all instances of and_gate
bind and_gate and_gate_sva u_and_gate_sva (.A(A), .B(B), .Y(Y));