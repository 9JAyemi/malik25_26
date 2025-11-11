// SVA for multiplexer. Bind this to the DUT for automatic checking/coverage.

module multiplexer_sva #(parameter int n = 1)
(
  input logic               ctrl,
  input logic [n-1:0]       D0,
  input logic [n-1:0]       D1,
  input logic [n-1:0]       S
);
  default clocking cb @(*); endclocking

  // Functional correctness (4-state exact behavior)
  assert property (S === (ctrl ? D1 : D0))
    else $error("MUX mismatch: ctrl=%b D0=%0h D1=%0h S=%0h", ctrl, D0, D1, S);

  // Control signal must be known (no X/Z)
  assert property (!$isunknown(ctrl))
    else $error("MUX ctrl is X/Z");

  // If all inputs known, output must be known
  assert property ((!$isunknown(D0) && !$isunknown(D1) && !$isunknown(ctrl)) |-> !$isunknown(S))
    else $error("MUX output X/Z with known inputs");

  // No glitches: stable inputs imply stable output
  assert property (($stable(ctrl) && $stable(D0) && $stable(D1)) |-> $stable(S))
    else $error("MUX glitch detected on S with stable inputs");

  // Branch coverage
  cover property (!ctrl && (S === D0));
  cover property ( ctrl && (S === D1));

  // Transition coverage on ctrl with correct output selection
  cover property ($rose(ctrl) && (S === D1));
  cover property ($fell(ctrl) && (S === D0));

  // Exercise both branches with differing data to ensure visible selection
  cover property ((D0 !== D1) && !ctrl && (S === D0) ##0 $rose(ctrl) && (S === D1));
endmodule

// Bind to DUT
bind multiplexer multiplexer_sva #(.n(n)) u_multiplexer_sva (
  .ctrl(ctrl),
  .D0  (D0),
  .D1  (D1),
  .S   (S)
);