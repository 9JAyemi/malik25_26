// SVA for Multiplexer_1bit
// Bind this to the DUT to check and cover key mux behavior concisely.

module Multiplexer_1bit_sva
  (input logic        ctrl,
   input logic [0:0]  D0,
   input logic [0:0]  D1,
   input logic [0:0]  S);

  // Functional correctness on any input change (sample next delta)
  assert property (@(ctrl or D0 or D1) ##0 (S === (ctrl ? D1 : D0)))
    else $error("MUX func mismatch: S != (ctrl?D1:D0)");

  // Deterministic paths when ctrl is known
  assert property (@(ctrl or D0 or D1) (ctrl === 1'b0) |-> ##0 (S === D0))
    else $error("MUX ctrl=0 path broken");
  assert property (@(ctrl or D0 or D1) (ctrl === 1'b1) |-> ##0 (S === D1))
    else $error("MUX ctrl=1 path broken");

  // If inputs are equal, output must equal them regardless of ctrl/X
  assert property (@(ctrl or D0 or D1) (D0 === D1) |-> ##0 (S === D0))
    else $error("MUX equal-input collapse violated");

  // X-propagation: if ctrl is X/Z and D0 != D1, S must be X
  assert property (@(ctrl or D0 or D1)
                   ((ctrl !== 1'b0) && (ctrl !== 1'b1) && (D0 !== D1)) |-> $isunknown(S))
    else $error("MUX X-prop violated for ctrl X and D0!=D1");

  // Non-selected input must not affect S (assuming selected input is stable)
  assert property (@(ctrl or D0 or D1)
                   (ctrl === 1'b0 && $changed(D1) && !$changed(D0)) |-> !$changed(S))
    else $error("MUX D1 perturbs S when ctrl=0");
  assert property (@(ctrl or D0 or D1)
                   (ctrl === 1'b1 && $changed(D0) && !$changed(D1)) |-> !$changed(S))
    else $error("MUX D0 perturbs S when ctrl=1");

  // On selected data change, S must immediately reflect it (next delta)
  assert property (@(ctrl or D0 or D1)
                   (ctrl === 1'b0 && $changed(D0)) |-> ##0 (S === D0))
    else $error("MUX failed to follow D0 when ctrl=0");
  assert property (@(ctrl or D0 or D1)
                   (ctrl === 1'b1 && $changed(D1)) |-> ##0 (S === D1))
    else $error("MUX failed to follow D1 when ctrl=1");

  // On ctrl change, S must switch to the newly selected input (next delta)
  assert property (@(ctrl) $changed(ctrl) |-> ##0 (S === (ctrl ? D1 : D0)))
    else $error("MUX failed to switch output on ctrl change");

  // Coverage: exercise both paths and values
  cover property (@(ctrl or D0 or D1) (ctrl===1'b0 && D0==1'b0) ##0 (S==1'b0));
  cover property (@(ctrl or D0 or D1) (ctrl===1'b0 && D0==1'b1) ##0 (S==1'b1));
  cover property (@(ctrl or D0 or D1) (ctrl===1'b1 && D1==1'b0) ##0 (S==1'b0));
  cover property (@(ctrl or D0 or D1) (ctrl===1'b1 && D1==1'b1) ##0 (S==1'b1));

  // Coverage: ctrl toggles, and X-merge case
  cover property (@(ctrl) $changed(ctrl));
  cover property (@(ctrl or D0 or D1)
                  ((ctrl !== 1'b0) && (ctrl !== 1'b1) && (D0 !== D1) && $isunknown(S)));

endmodule

bind Multiplexer_1bit Multiplexer_1bit_sva mux_1bit_sva_i(.ctrl(ctrl), .D0(D0), .D1(D1), .S(S));