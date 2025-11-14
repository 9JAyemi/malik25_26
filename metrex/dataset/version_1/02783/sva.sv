// SVA for OR_gate. Bind this to the DUT.
module OR_gate_sva (input logic a, b, out);

  // Functional equivalence at 0-delay on any relevant change
  property p_func_or;
    @(a or b or out) ##0 (out === (a || b));
  endproperty
  assert property (p_func_or) else $error("OR_gate: out != (a||b)");

  // Inputs must be known when they change (avoid X/Z optimism in if(a||b))
  property p_inputs_known_on_change;
    @(a or b) !$isunknown(a) && !$isunknown(b);
  endproperty
  assert property (p_inputs_known_on_change) else $error("OR_gate: X/Z on inputs");

  // Output must be known after any input change
  property p_out_known_after_input;
    @(a or b) ##0 !$isunknown(out);
  endproperty
  assert property (p_out_known_after_input) else $error("OR_gate: out is X/Z after input change");

  // No spurious output change without an input change
  property p_no_spurious_out_change;
    @(out) ##0 ($changed(a) || $changed(b));
  endproperty
  assert property (p_no_spurious_out_change) else $error("OR_gate: out changed without input change");

  // Functional coverage: all input combinations observed with correct out
  cover property (@(a or b) ##0 (!a && !b && !out));
  cover property (@(a or b) ##0 (!a &&  b &&  out));
  cover property (@(a or b) ##0 ( a && !b &&  out));
  cover property (@(a or b) ##0 ( a &&  b &&  out));

  // Output toggle coverage
  cover property (@(a or b or out) $rose(out));
  cover property (@(a or b or out) $fell(out));

endmodule

bind OR_gate OR_gate_sva sva_or (.*);