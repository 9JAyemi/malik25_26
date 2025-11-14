// SVA for my_d_latch: edge-triggered capture on posedge GATE

module my_d_latch_sva (input logic D, GATE, Q);

  // Sample on the DUT clock
  default clocking cb @(posedge GATE); endclocking

  // Correct capture: after the first edge, Q equals D from the previous edge
  a_capture:     assert property ( $past(GATE) |-> Q == $past(D) );

  // Q must not go X if previous D was known
  a_known_q:     assert property ( $past(GATE) && !$isunknown($past(D)) |-> !$isunknown(Q) );

  // Q changes only in conjunction with a GATE posedge (no asynchronous glitches)
  a_q_only_on_gate: assert property (@(posedge Q or negedge Q) $rose(GATE));

  // If D matched Q at the prior edge, Q must hold its value across this edge
  a_hold_when_match: assert property ( $past(GATE) && ($past(D) == $past(Q)) |-> Q == $past(Q) );

  // GATE must not be X/Z on its edges
  a_gate_clean:  assert property (@(posedge GATE or negedge GATE) !$isunknown(GATE));

  // Coverage: capture of 0 and 1, Q toggling, and D activity across edges
  c_cap0:        cover  property ( D==0 ##1 Q==0 );
  c_cap1:        cover  property ( D==1 ##1 Q==1 );
  c_q_toggle:    cover  property ( $changed(Q) );
  c_d_activity:  cover  property ( ($rose(D) ##1 1) or ($fell(D) ##1 1) );

endmodule

// Bind into DUT
bind my_d_latch my_d_latch_sva sva_inst (.*);