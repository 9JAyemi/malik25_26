// SVA checker for Multiplexer; bind to DUT instance(s) as shown below.
module Multiplexer_sva #(parameter int N = 1)
(
  input logic [N-1:0] D0,
  input logic [N-1:0] D1,
  input logic         ctrl,
  input logic [N-1:0] S
);

  // Core functional check (4-state accurate, covers ctrl=X/Z)
  assert property (@(D0 or D1 or ctrl or S)
                   S === ((D1 & {N{ctrl}}) | (D0 & ~{N{ctrl}})))
    else $error("Multiplexer: functional mismatch");

  // No spontaneous output change without a driving change
  assert property (@(D0 or D1 or ctrl or S)
                   $changed(S) |-> ($changed(ctrl) or $changed(D0) or $changed(D1)))
    else $error("Multiplexer: S changed without ctrl/D change");

  // Coverage: both selections exercised when they matter (D0 != D1)
  cover property (@(D0 or D1 or ctrl)
                  (D0 !== D1) && (ctrl == 1'b0) && (S === D0));
  cover property (@(D0 or D1 or ctrl)
                  (D0 !== D1) && (ctrl == 1'b1) && (S === D1));

  // Coverage: ctrl toggles while data differ and S follows the selected input
  cover property (@(posedge ctrl)
                  (D0 !== D1) && (S === D1));
  cover property (@(negedge ctrl)
                  (D0 !== D1) && (S === D0));

  // Coverage: unknown ctrl propagates X on bits where D0 and D1 differ
  cover property (@(D0 or D1 or ctrl)
                  (ctrl !== 1'b0) && (ctrl !== 1'b1) &&
                  (|(D0 ^ D1)) && $isunknown(S));

endmodule

// Example bind (place in a package or a separate file compiled with the DUT):
// bind Multiplexer Multiplexer_sva #(.N(N)) Multiplexer_sva_i (.*);