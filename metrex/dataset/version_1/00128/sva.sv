// SVA for xor_gate — concise, high-quality checks and coverage

module xor_gate_sva (input logic a, b, out_assign);

  // Functional correctness on known inputs
  property p_xor_func;
    @(a or b or out_assign) !$isunknown({a,b}) |-> (out_assign === (a ^ b));
  endproperty
  assert property (p_xor_func);

  // Unknown/Z propagation: any unknown input makes output unknown
  property p_xor_xprop;
    @(a or b or out_assign) $isunknown({a,b}) |-> $isunknown(out_assign);
  endproperty
  assert property (p_xor_xprop);

  // No spurious output changes (output changes only if an input changed)
  property p_no_spurious_glitch;
    @(a or b or out_assign) $changed(out_assign) |-> ($changed(a) || $changed(b));
  endproperty
  assert property (p_no_spurious_glitch);

  // Truth-table coverage
  cover property (@(a or b or out_assign) (a==0 && b==0 && out_assign==0));
  cover property (@(a or b or out_assign) (a==0 && b==1 && out_assign==1));
  cover property (@(a or b or out_assign) (a==1 && b==0 && out_assign==1));
  cover property (@(a or b or out_assign) (a==1 && b==1 && out_assign==0));

  // Toggle coverage: output toggles when exactly one input toggles
  cover property (@(a) $changed(a) && !$changed(b) && $changed(out_assign));
  cover property (@(b) $changed(b) && !$changed(a) && $changed(out_assign));

endmodule

// Bind into all xor_gate instances
bind xor_gate xor_gate_sva xor_gate_sva_i (.a(a), .b(b), .out_assign(out_assign));