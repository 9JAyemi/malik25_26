// SVA for d_ff_async_reset_sync_set
// Captures intended synchronous enable + gated reset behavior,
// ensures no change on negedge E, and provides concise coverage.

module d_ff_async_reset_sync_set_sva (
  input logic C,
  input logic D,
  input logic R,
  input logic E,
  input logic Q
);

  default clocking cb @(posedge C); endclocking

  bit past_valid;
  initial past_valid = 1'b0;
  always @(posedge C) past_valid <= 1'b1;

  // Functional truth table at posedge C:
  // - If E==0: hold
  // - Else if R==1: Q=0
  // - Else Q=D
  property p_update;
    past_valid |-> ( E ? (R ? (Q == 1'b0) : (Q == D))
                       : (Q == $past(Q)) );
  endproperty
  assert property (p_update);

  // Despite async sensitivity on negedge E, Q must not change there
  assert property (@(negedge E) $stable(Q));

  // Q changes only on posedge C (relative to C/E activity)
  assert property (@(posedge C or negedge E) (!$changed(Q)) or $rose(C));

  // No X/Z on Q once we have at least one sampled cycle
  assert property (past_valid |-> !$isunknown(Q));

  // Coverage
  cover property (@(posedge C) past_valid && E && !R && (Q == D));      // normal capture
  cover property (@(posedge C) past_valid && E && R  && (Q == 1'b0));   // gated reset active
  cover property (@(posedge C) past_valid && !E && (Q == $past(Q)));    // hold on E==0
  cover property (@(negedge E) $stable(Q));                              // no change on async edge
  // Masked reset when E==0 followed by update when E==1
  cover property (@(posedge C) past_valid && !E ##1 E && !R);

endmodule

bind d_ff_async_reset_sync_set d_ff_async_reset_sync_set_sva u_sva (
  .C(C), .D(D), .R(R), .E(E), .Q(Q)
);