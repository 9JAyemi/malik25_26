// SVA for Multiplexer
module Multiplexer_sva (
  input logic        ctrl,
  input logic [0:0]  D0,
  input logic [0:0]  D1,
  input logic [0:0]  S
);

  // Functional correctness: output matches selected input (after delta cycle)
  property p_mux_func;
    @(ctrl or D0 or D1) 1 |-> ##0 (S === (ctrl ? D1 : D0));
  endproperty
  assert property (p_mux_func);

  // Control must be known to avoid latch behavior from incomplete case
  property p_ctrl_known;
    @(ctrl or D0 or D1 or S) !$isunknown(ctrl);
  endproperty
  assert property (p_ctrl_known);

  // Isolation: unselected input must not affect S
  property p_d1_isolation;
    @(D1) (ctrl === 1'b0) |-> ##0 $stable(S);
  endproperty
  assert property (p_d1_isolation);

  property p_d0_isolation;
    @(D0) (ctrl === 1'b1) |-> ##0 $stable(S);
  endproperty
  assert property (p_d0_isolation);

  // Any S change must be justified by ctrl or selected input change
  property p_s_change_reason;
    @(S) $changed(S) |-> ##0 (
        $changed(ctrl) ||
        ((ctrl === 1'b0) && $changed(D0)) ||
        ((ctrl === 1'b1) && $changed(D1))
    );
  endproperty
  assert property (p_s_change_reason);

  // If ctrl and selected input are known, S must be known
  property p_known_out_when_known_in;
    @(ctrl or D0 or D1)
      (!$isunknown(ctrl) && !$isunknown((ctrl ? D1 : D0)))
      |-> ##0 (!$isunknown(S));
  endproperty
  assert property (p_known_out_when_known_in);

  // Coverage: exercise both selects and both data paths
  cover property (@(posedge ctrl) 1);
  cover property (@(negedge ctrl) 1);
  cover property (@(D0) (ctrl === 1'b0) ##0 $changed(S));
  cover property (@(D1) (ctrl === 1'b1) ##0 $changed(S));

endmodule

// Bind into DUT
bind Multiplexer Multiplexer_sva sva (
  .ctrl(ctrl),
  .D0  (D0),
  .D1  (D1),
  .S   (S)
);