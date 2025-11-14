// SVA for mux_2to1. Bind this to the DUT.

module mux_2to1_sva (
  input logic a,
  input logic b,
  input logic sel,
  input logic out_always
);

  // Functional correctness on any input change (sampled post-delta)
  property p_mux_func;
    @(a or b or sel) 1 |-> ##0 (out_always === (sel ? b : a));
  endproperty
  assert property (p_mux_func);

  // Output follows data inputs when selected
  assert property (@(a) (sel === 1'b0) && $changed(a) |-> ##0 (out_always === a));
  assert property (@(b) (sel === 1'b1) && $changed(b) |-> ##0 (out_always === b));

  // Output follows select edges
  assert property (@(sel) $rose(sel) |-> ##0 (out_always === b));
  assert property (@(sel) $fell(sel) |-> ##0 (out_always === a));

  // Knownness: if inputs are known, output must be known
  assert property (@(a or b or sel) !$isunknown({a,b,sel}) |-> ##0 !$isunknown(out_always));

  // Coverage: exercise both paths and key transitions
  cover property (@(a or b or sel) sel===1'b0 ##0 (out_always===a));
  cover property (@(a or b or sel) sel===1'b1 ##0 (out_always===b));
  cover property (@(sel) $rose(sel) && (a!==b) ##0 (out_always===b));
  cover property (@(sel) $fell(sel) && (a!==b) ##0 (out_always===a));
  cover property (@(a) sel===1'b0 && $changed(a) ##0 (out_always===a));
  cover property (@(b) sel===1'b1 && $changed(b) ##0 (out_always===b));
  cover property (@(sel) $changed(sel) && (a===b) ##0 $stable(out_always));

endmodule

bind mux_2to1 mux_2to1_sva sva_mux_2to1 (.a(a), .b(b), .sel(sel), .out_always(out_always));