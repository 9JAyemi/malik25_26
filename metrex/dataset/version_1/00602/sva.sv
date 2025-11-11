// SVA for xor_gate: concise, full functional checks and coverage
module xor_gate_sva (input logic A, B, X);

  // Sample on any relevant edge (inputs or output)
  default clocking cb @(posedge A or negedge A or posedge B or negedge B or posedge X or negedge X); endclocking

  // Functional correctness when inputs are known
  property p_func_known;
    (A inside {1'b0,1'b1} && B inside {1'b0,1'b1}) |-> (X === (A ^ B));
  endproperty
  assert property (p_func_known) else $error("X != A^B with known inputs");

  // Output must not be X unless at least one input is X/Z
  property p_no_spurious_x;
    (X === 1'bx) |-> !(A inside {1'b0,1'b1} && B inside {1'b0,1'b1});
  endproperty
  assert property (p_no_spurious_x) else $error("Output X unknown with known inputs");

  // Exactly one input toggle causes X to toggle (after delta)
  property p_one_toggle_toggles;
    (A inside {1'b0,1'b1} && B inside {1'b0,1'b1} && ($changed(A) ^ $changed(B))) |-> ##0 $changed(X);
  endproperty
  assert property (p_one_toggle_toggles) else $error("X did not toggle on single-input toggle");

  // Both inputs toggle in same tick => X holds (after delta)
  property p_both_toggle_holds;
    (A inside {1'b0,1'b1} && B inside {1'b0,1'b1} && $changed(A) && $changed(B)) |-> ##0 !$changed(X);
  endproperty
  assert property (p_both_toggle_holds) else $error("X changed when both inputs toggled together");

  // Any X change must be caused by an input change in the same tick
  property p_x_change_has_cause;
    $changed(X) |-> ($changed(A) || $changed(B));
  endproperty
  assert property (p_x_change_has_cause) else $error("X changed without input change");

  // Truth-table coverage (only counts when correct)
  cover property (A==1'b0 && B==1'b0 && X==1'b0);
  cover property (A==1'b0 && B==1'b1 && X==1'b1);
  cover property (A==1'b1 && B==1'b0 && X==1'b1);
  cover property (A==1'b1 && B==1'b1 && X==1'b0);

  // Toggle behavior coverage
  cover property ((A inside {1'b0,1'b1} && B inside {1'b0,1'b1} && ($changed(A) ^ $changed(B))) ##0 $changed(X));
  cover property ((A inside {1'b0,1'b1} && B inside {1'b0,1'b1} && $changed(A) && $changed(B)) ##0 !$changed(X));

endmodule

// Bind to DUT
bind xor_gate xor_gate_sva xor_gate_sva_i(.A(A), .B(B), .X(X));