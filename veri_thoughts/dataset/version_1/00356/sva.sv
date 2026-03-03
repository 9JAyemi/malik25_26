// SVA for Multiplexer_2_1_parameterized1
// Bind these assertions to the DUT; no DUT/testbench code beyond bind.

module Multiplexer_2_1_parameterized1_sva
(
  input  logic        ctrl,
  input  logic [0:0]  D0,
  input  logic [0:0]  D1,
  input  logic [0:0]  S
);

  // Functional equivalence incl. X-propagation/merge semantics
  a_func: assert property (
    S === ((ctrl===1'b0) ? D0 :
           (ctrl===1'b1) ? D1 :
           ((D0===D1) ? D0 : 1'bx))
  );

  // Known-output when selected input and ctrl are known
  a_sel0_known: assert property ((ctrl===1'b0 && !$isunknown(D0)) |-> (!$isunknown(S) && S===D0));
  a_sel1_known: assert property ((ctrl===1'b1 && !$isunknown(D1)) |-> (!$isunknown(S) && S===D1));

  // Independence from unselected input
  a_ignore_d1: assert property (($changed(D1) && ctrl===1'b0) |-> $stable(S));
  a_ignore_d0: assert property (($changed(D0) && ctrl===1'b1) |-> $stable(S));

  // Basic functional coverage (all select/data combinations and X-merge behavior)
  c_sel0_0:  cover property (ctrl===1'b0 && D0===1'b0 && S===1'b0);
  c_sel0_1:  cover property (ctrl===1'b0 && D0===1'b1 && S===1'b1);
  c_sel1_0:  cover property (ctrl===1'b1 && D1===1'b0 && S===1'b0);
  c_sel1_1:  cover property (ctrl===1'b1 && D1===1'b1 && S===1'b1);
  c_xmerge:  cover property ((ctrl!==1'b0 && ctrl!==1'b1) && (D0!==D1) && $isunknown(S));
  c_xresolve: cover property ((ctrl!==1'b0 && ctrl!==1'b1) && (D0===D1) && (S===D0));

endmodule

bind Multiplexer_2_1_parameterized1 Multiplexer_2_1_parameterized1_sva sva_i(.*);