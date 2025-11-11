// SVA for reg3_sync_reset
// Focus: synchronous reset to 0 and data capture on rising clock, X-propagation checks, and concise coverage.

module reg3_sync_reset_sva (
  input logic       CLK,
  input logic       RST,
  input logic [2:0] D,
  input logic [2:0] Q
);
  default clocking cb @(posedge CLK); endclocking

  // Reset takes effect on the next sampled cycle and holds while asserted
  property p_reset_sync;
    $past(RST) |-> (Q == 3'b000);
  endproperty
  assert property (p_reset_sync);

  // Normal operation: when not in reset, Q follows previous D
  property p_follow_d;
    !$past(RST) |-> (Q == $past(D));
  endproperty
  assert property (p_follow_d);

  // Q should never be X/Z after a clock; reset should clean Xs
  assert property (!$isunknown(Q));

  // If we captured data (not in reset), the captured D must have been known
  // (prevents propagating X into state)
  assert property (!$past(RST) |-> !$isunknown($past(D)));

  // Optional sanity: when both D and RST hold, Q holds
  property p_hold_when_inputs_hold;
    (!$past(RST) && (D == $past(D))) |-> (Q == $past(Q));
  endproperty
  assert property (p_hold_when_inputs_hold);

  // Coverage: see a reset pulse followed by a non-zero update
  cover property (RST ##1 !RST ##1 (Q != 3'b000));

  // Coverage: observe Q capturing a change on D
  cover property ((!RST && $changed(D)) ##1 (Q == $past(D)));

endmodule

// Bind into DUT
bind reg3_sync_reset reg3_sync_reset_sva sva_i (.CLK(CLK), .RST(RST), .D(D), .Q(Q));