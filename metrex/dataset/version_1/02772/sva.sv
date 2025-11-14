// SVA for Multiplexer. Bind this to the DUT.
// Concise checks: functional equivalence, X-semantics, no spurious toggles, plus coverage.

module multiplexer_sva (input ctrl, input D0, input D1, input S);

  // Sample on any edge of relevant signals
  default clocking cb @(
      posedge ctrl or negedge ctrl or
      posedge D0   or negedge D0   or
      posedge D1   or negedge D1   or
      posedge S    or negedge S
  ); endclocking

  // Functional equivalence (4-state aware)
  assert property (S === (ctrl ? D1 : D0));

  // Output known if all inputs are known
  assert property ((!$isunknown(ctrl) && !$isunknown(D0) && !$isunknown(D1)) |-> !$isunknown(S));

  // 4-state mux semantics when select is X/Z:
  // If data inputs differ, result must be X; if equal, result must be that value.
  assert property (($isunknown(ctrl) && (D0 !== D1)) |-> (S === 1'bx));
  assert property ((D0 === D1) |-> (S === D0));

  // No spurious output toggle without an input or select toggle
  assert property ($changed(S) |-> ($changed(ctrl) || $changed(D0) || $changed(D1)));

  // Coverage: exercise both data values through each select, and X-select behaviors
  cover property (ctrl === 1'b0 && D0 === 1'b0 && S === 1'b0);
  cover property (ctrl === 1'b0 && D0 === 1'b1 && S === 1'b1);
  cover property (ctrl === 1'b1 && D1 === 1'b0 && S === 1'b0);
  cover property (ctrl === 1'b1 && D1 === 1'b1 && S === 1'b1);
  cover property ($isunknown(ctrl) && (D0 !== D1) && (S === 1'bx));
  cover property ($isunknown(ctrl) && (D0 === D1) && (S === D0));

endmodule

// Bind into the DUT
bind Multiplexer multiplexer_sva u_multiplexer_sva (.*);