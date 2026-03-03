// SVA for Multiplexer_AC__parameterized57
module Multiplexer_AC__parameterized57_sva
(
  input logic       ctrl,
  input logic [0:0] D0,
  input logic [0:0] D1,
  input logic [0:0] S
);
  default clocking cb @($global_clock); endclocking

  // Functional equivalence (4-state accurate)
  assert property (S[0] == (ctrl ? D1[0] : D0[0]));

  // Selected path correctness
  assert property ((ctrl === 1'b0) |-> (S[0] == D0[0]));
  assert property ((ctrl === 1'b1) |-> (S[0] == D1[0]));

  // Propagation from selected input
  assert property ((ctrl === 1'b0 && $changed(D0[0])) |-> $changed(S[0]));
  assert property ((ctrl === 1'b1 && $changed(D1[0])) |-> $changed(S[0]));

  // No effect from unselected input
  assert property ((ctrl === 1'b0 && $changed(D1[0])) |-> $stable(S[0]));
  assert property ((ctrl === 1'b1 && $changed(D0[0])) |-> $stable(S[0]));

  // Output known when select and selected data are known
  assert property ((!$isunknown(ctrl) && (ctrl ? !$isunknown(D1[0]) : !$isunknown(D0[0])))
                   |-> !$isunknown(S[0]));

  // Coverage
  cover property (ctrl === 1'b0);
  cover property (ctrl === 1'b1);
  cover property (ctrl === 1'b0 ##1 ctrl === 1'b1);
  cover property (ctrl === 1'b1 ##1 ctrl === 1'b0);
  cover property (ctrl === 1'b0 && $changed(D0[0]) && $changed(S[0]));
  cover property (ctrl === 1'b1 && $changed(D1[0]) && $changed(S[0]));
  cover property (ctrl === 1'b0 && $changed(D1[0]) && $stable(S[0]));
  cover property (ctrl === 1'b1 && $changed(D0[0]) && $stable(S[0]));
endmodule

bind Multiplexer_AC__parameterized57 Multiplexer_AC__parameterized57_sva
(
  .ctrl(ctrl),
  .D0(D0),
  .D1(D1),
  .S(S)
);