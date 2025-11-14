// SVA for d_latch
module d_latch_sva (
  input logic D,
  input logic S,
  input logic R,
  input logic CLK,
  input logic Q
);

  default clocking cb @(posedge CLK); endclocking

  // Golden next-state relation (uses previous-cycle inputs)
  property p_next;
    $past(1'b1) |-> Q == ($past(R) ? 1'b0 : ($past(S) ? 1'b1 : $past(D)));
  endproperty
  assert property (p_next);

  // Explicit R-over-S priority when both high
  assert property ($past(1'b1) && $past(R && S) |-> Q == 1'b0);

  // Q may only change on a rising edge of CLK
  assert property (@(posedge Q or negedge Q) $rose(CLK));

  // No X/Z on key signals at meaningful sample times
  assert property (!$isunknown({R,S,D}));
  assert property ($past(1'b1) |-> !$isunknown(Q));

  // Functional coverage of all branches
  cover property (R);
  cover property (S && !R);
  cover property (!R && !S && D);
  cover property (!R && !S && !D);
  cover property (R && S);

endmodule

bind d_latch d_latch_sva u_d_latch_sva (.D(D), .S(S), .R(R), .CLK(CLK), .Q(Q));