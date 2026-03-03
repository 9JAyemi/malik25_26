// SVA for dff: concise, full behavioral checks and coverage
module dff_sva #(parameter INIT = 1'b0) (
  input logic Q, D, C, E, R, S
);

  default clocking cb @(posedge C); endclocking

  // Make $past safe
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge C) past_valid <= 1'b1;

  // Q must never be X/Z at clock edges
  a_q_known: assert property ( !$isunknown(Q) );

  // Synchronous priority and behavior (use previous-cycle controls)
  a_reset: assert property ( disable iff (!past_valid)
                             !$past(R) |-> (Q == INIT) );

  a_set:   assert property ( disable iff (!past_valid)
                             ($past(R) && !$past(S)) |-> (Q == 1'b1) );

  a_en:    assert property ( disable iff (!past_valid)
                             ($past(R) && $past(S) && $past(E)) |-> (Q == $past(D)) );

  a_hold:  assert property ( disable iff (!past_valid)
                             ($past(R) && $past(S) && !$past(E)) |-> (Q == $past(Q)) );

  // When both R and S are low, reset has priority (explicitly checked)
  a_rs_both_low_pri: assert property ( disable iff (!past_valid)
                                       (!$past(R) && !$past(S)) |-> (Q == INIT) );

  // Q may only change coincident with C posedge (no glitches)
  a_q_only_changes_on_c: assert property (@(posedge Q or negedge Q) $rose(C));

  // Coverage: hit all key behaviors
  c_reset:   cover property ( disable iff (!past_valid)
                              !$past(R) ##1 (Q == INIT) );

  c_set:     cover property ( disable iff (!past_valid)
                              ($past(R) && !$past(S)) ##1 (Q == 1'b1) );

  c_hold:    cover property ( disable iff (!past_valid)
                              ($past(R) && $past(S) && !$past(E)) ##1 (Q == $past(Q)) );

  // Enable-driven 0->1 and 1->0 updates
  c_en_01:   cover property ( disable iff (!past_valid)
                              ($past(R) && $past(S) && $past(E) &&
                               ($past(Q)==1'b0) && ($past(D)==1'b1)) ##1 (Q==1'b1) );

  c_en_10:   cover property ( disable iff (!past_valid)
                              ($past(R) && $past(S) && $past(E) &&
                               ($past(Q)==1'b1) && ($past(D)==1'b0)) ##1 (Q==1'b0) );

  // Both controls low in same cycle (priority exercised)
  c_rs_both_low: cover property ( disable iff (!past_valid)
                                  (!$past(R) && !$past(S)) ##1 (Q == INIT) );

endmodule

// Bind example:
// bind dff dff_sva #(.INIT(INIT)) dff_sva_i (.Q(Q), .D(D), .C(C), .E(E), .R(R), .S(S));