// SVA for my_module — concise, full functional checks and coverage
module my_module_sva (input A1, input A2, input X, input and0_out_X);

  // Event-based sampling on any relevant change
  default clocking cb @(A1 or A2 or X or and0_out_X); endclocking

  // Functional correctness (gate, buffer, and overall)
  a_and_func:   assert property (and0_out_X === (A1 & A2))
                  else $error("and0_out_X != (A1 & A2)");
  a_buf_func:   assert property (X === and0_out_X)
                  else $error("X != and0_out_X");
  a_overall:    assert property (X === (A1 & A2))
                  else $error("X != (A1 & A2)");

  // Known-in -> known-and-correct-out
  a_known_out:  assert property (!$isunknown({A1,A2}) |-> (!$isunknown(and0_out_X) && !$isunknown(X) && X == (A1 & A2)))
                  else $error("Known inputs did not yield known, correct output");

  // Causality/glitch sanity
  a_x_has_cause:     assert property ($changed(X) |-> $changed(and0_out_X))
                       else $error("X changed without and0_out_X changing");
  a_and_has_cause:   assert property ($changed(and0_out_X) |-> ($changed(A1) || $changed(A2)))
                       else $error("and0_out_X changed without A1/A2 changing");
  a_no_spurious_out: assert property ((!$changed({A1,A2})) |-> (!$changed(X)))
                       else $error("X changed while A1/A2 were stable");

  // Functional coverage: all input combos and output, plus toggles
  c_00: cover property (A1==0 && A2==0 && X==0);
  c_01: cover property (A1==0 && A2==1 && X==0);
  c_10: cover property (A1==1 && A2==0 && X==0);
  c_11: cover property (A1==1 && A2==1 && X==1);
  c_x_toggle:     cover property ($changed(X));
  c_and_toggle:   cover property ($changed(and0_out_X));

endmodule

// Bind into DUT scope (and0_out_X is internal; bind sees it in the instance scope)
bind my_module my_module_sva sva_i(.A1(A1), .A2(A2), .X(X), .and0_out_X(and0_out_X));