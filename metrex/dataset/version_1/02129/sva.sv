// SVA for and_gate
module and_gate_sva (
  input logic A, B, C,
  input logic Y,
  input logic VDD, VSS
);
  // Sample on any relevant change
  default clocking cb @(A or B or C or Y or VDD or VSS); endclocking

  // Functional correctness (X-safe on inputs)
  property p_and_fn;
    !$isunknown({A,B,C}) |-> (Y === (A & B & C));
  endproperty
  assert property (p_and_fn);

  // Power rails integrity
  assert property (VDD === 1'b1);
  assert property (VSS === 1'b0);

  // Output mirrors each input when the other two are 1
  assert property (B && C && $rose(A) |-> $rose(Y));
  assert property (B && C && $fell(A) |-> $fell(Y));
  assert property (A && C && $rose(B) |-> $rose(Y));
  assert property (A && C && $fell(B) |-> $fell(Y));
  assert property (A && B && $rose(C) |-> $rose(Y));
  assert property (A && B && $fell(C) |-> $fell(Y));

  // No spurious output transitions
  assert property ($rose(Y) |-> (A && B && C));
  assert property ($fell(Y) |-> !(A && B && C));

  // Functional coverage: all input combinations with expected Y
  cover property (!A && !B && !C && (Y==0));
  cover property (!A && !B &&  C && (Y==0));
  cover property (!A &&  B && !C && (Y==0));
  cover property (!A &&  B &&  C && (Y==0));
  cover property ( A && !B && !C && (Y==0));
  cover property ( A && !B &&  C && (Y==0));
  cover property ( A &&  B && !C && (Y==0));
  cover property ( A &&  B &&  C && (Y==1));

  // Output edge coverage
  cover property ($rose(Y));
  cover property ($fell(Y));
endmodule

// Bind into DUT
bind and_gate and_gate_sva and_gate_sva_i (.A(A), .B(B), .C(C), .Y(Y), .VDD(VDD), .VSS(VSS));