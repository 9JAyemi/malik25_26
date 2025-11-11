// SVA checker for mux2to1_behav
module mux2to1_behav_sva (input logic a, b, sel, out);

  // Functional correctness (captures 4-state semantics)
  property p_func;
    @(a or b or sel or out) 1 |-> ##0 (out === (sel ? b : a));
  endproperty
  assert property (p_func)
    else $error("mux2to1_behav: out != (sel ? b : a)");

  // If inputs are known, output must be known
  property p_no_x_when_inputs_known;
    @(a or b or sel) (!$isunknown({a,b,sel})) |-> ##0 (!$isunknown(out));
  endproperty
  assert property (p_no_x_when_inputs_known)
    else $error("mux2to1_behav: out is X/Z while a,b,sel are known");

  // No spurious out change without a/b/sel change
  property p_no_spurious_out_change;
    @(out) $changed(out) |-> ($changed(a) or $changed(b) or $changed(sel));
  endproperty
  assert property (p_no_spurious_out_change)
    else $error("mux2to1_behav: out changed without a/b/sel change");

  // Explicit 4-state corner semantics for unknown sel
  property p_sel_x_equal_inputs;
    @(a or b or sel) ($isunknown(sel) && (a===b) && !$isunknown(a)) |-> ##0 (out===a);
  endproperty
  assert property (p_sel_x_equal_inputs)
    else $error("mux2to1_behav: sel X with equal inputs should pass through");

  property p_sel_x_unequal_inputs;
    @(a or b or sel) ($isunknown(sel) && (a!==b)) |-> ##0 $isunknown(out);
  endproperty
  assert property (p_sel_x_unequal_inputs)
    else $error("mux2to1_behav: sel X with unequal inputs should yield X out");

  // Coverage: exercise both paths, select toggles, and X-select behavior
  cover property (@(a or b or sel) (sel===1'b0 && !$isunknown(a)) ##0 (out===a));
  cover property (@(a or b or sel) (sel===1'b1 && !$isunknown(b)) ##0 (out===b));
  cover property (@(posedge sel) (!$isunknown({a,b}) && (a!=b)) ##0 (out===b));
  cover property (@(negedge sel) (!$isunknown({a,b}) && (a!=b)) ##0 (out===a));
  cover property (@(a or b or sel) ($isunknown(sel) && (a===b) && !$isunknown(a)) ##0 (out===a));
  cover property (@(a or b or sel) ($isunknown(sel) && (a!==b)) ##0 $isunknown(out));

endmodule

bind mux2to1_behav mux2to1_behav_sva sva_mux2to1 (.a(a), .b(b), .sel(sel), .out(out));