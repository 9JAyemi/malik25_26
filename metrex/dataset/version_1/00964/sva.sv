// SVA for xor_gate
// Bind this to the DUT; focuses on correctness, X-safety, and coverage of truth table.

bind xor_gate xor_gate_sva i_xor_gate_sva (.a(a), .b(b), .out(out));

module xor_gate_sva(input logic a, b, out);

  // Functional equivalence (sample after comb update)
  property p_xor_func;
    @(a or b) 1'b1 |-> ##0 (out === (a ^ b));
  endproperty
  assert property (p_xor_func);

  // Inputs should be known (no X/Z) whenever they change
  property p_inputs_known;
    @(a or b) ##0 (!$isunknown(a) && !$isunknown(b));
  endproperty
  assert property (p_inputs_known);

  // Output should never go X/Z
  property p_out_known;
    @(a or b or out) ##0 !$isunknown(out);
  endproperty
  assert property (p_out_known);

  // Any out change must be caused by an input change in the same timestep
  property p_out_change_has_cause;
    @(out) 1'b1 |-> ##0 ($changed(a) || $changed(b));
  endproperty
  assert property (p_out_change_has_cause);

  // Truth-table coverage (all 4 cases with correct out)
  cover property (@(a or b) ##0 (a===1'b0 && b===1'b0 && out===1'b0));
  cover property (@(a or b) ##0 (a===1'b0 && b===1'b1 && out===1'b1));
  cover property (@(a or b) ##0 (a===1'b1 && b===1'b0 && out===1'b1));
  cover property (@(a or b) ##0 (a===1'b1 && b===1'b1 && out===1'b0));

  // Toggle coverage: each input toggle causes out to reevaluate
  cover property (@(posedge a or negedge a) ##0 $changed(out));
  cover property (@(posedge b or negedge b) ##0 $changed(out));

endmodule