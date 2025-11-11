// SVA for my_logic_gate
// Bind this checker to the DUT to verify functionality and provide concise coverage.

module my_logic_gate_sva (
  input  logic A1, A2, B1, C1, D1,
  input  logic and1, and2,
  input  logic Y
);
  // Helper: inputs are all known
  function automatic bit inputs_known();
    return !$isunknown({A1,A2,B1,C1,D1});
  endfunction

  // Internal path correctness
  property p_and1_func; @(A1 or A2 or B1 or C1 or D1) ##0 (and1 == (A1 & A2 & B1 & C1 & D1)); endproperty
  assert property (p_and1_func);

  property p_and2_func; @(B1 or C1 or D1 or A1 or A2) ##0 (and2 == (B1 & C1 & D1)); endproperty
  assert property (p_and2_func);

  // OR gate structure (internal connectivity)
  property p_Y_struct; @(and1 or and2) ##0 (Y == (and1 | and2)); endproperty
  assert property (p_Y_struct);

  // Black-box functional equivalence (reduces to Y == B1&C1&D1)
  property p_Y_min_func; @(A1 or A2 or B1 or C1 or D1) ##0 (Y == (B1 & C1 & D1)); endproperty
  assert property (p_Y_min_func);

  // Knownness: if inputs known, outputs/internal nets must be known after settle
  property p_knownness;
    @(A1 or A2 or B1 or C1 or D1)
      inputs_known() |-> ##0 (!$isunknown(and1) && !$isunknown(and2) && !$isunknown(Y));
  endproperty
  assert property (p_knownness);

  // Minimal, high-value coverage
  // Y asserts (via either path)
  cover property (@(A1 or A2 or B1 or C1 or D1) (B1 & C1 & D1) ##0 (Y && and2));
  // Only secondary path active (and2=1, and1=0)
  cover property (@(A1 or A2 or B1 or C1 or D1) (B1 & C1 & D1 & !(A1 & A2)) ##0 (Y && and2 && !and1));
  // Both paths active
  cover property (@(A1 or A2 or B1 or C1 or D1) (A1 & A2 & B1 & C1 & D1) ##0 (Y && and1 && and2));
  // Y deasserts
  cover property (@(A1 or A2 or B1 or C1 or D1) inputs_known() && !(B1 & C1 & D1) ##0 (!Y));
  // Y edges
  cover property (@(A1 or A2 or B1 or C1 or D1) ##0 $rose(Y));
  cover property (@(A1 or A2 or B1 or C1 or D1) ##0 $fell(Y));
endmodule

bind my_logic_gate my_logic_gate_sva sva_inst (.*);