// SVA for TFFSR
module TFFSR_sva (input logic D, S, R, CLK, Q, QN);

  default clocking cb @(posedge CLK); endclocking

  // Next-state functional checks (based on previous-cycle inputs)
  ap_set:       assert property ( $past(S)                 |-> (Q==1'b1 && QN==1'b0) );
  ap_reset:     assert property ( $past(!S && R)           |-> (Q==1'b0 && QN==1'b1) );
  ap_priority:  assert property ( $past(S && R)            |-> (Q==1'b1 && QN==1'b0) );
  ap_func:      assert property ( $past(!S && !R)          |-> (Q == ($past(D) ^ $past(Q)) && QN == ~($past(Q))) );

  // Outputs must be 1-bit known on each clock
  ap_no_xz_out: assert property ( !$isunknown({Q,QN}) );

  // Outputs only change on clock edges
  ap_sync_only_q:  assert property ( @(posedge Q  or negedge Q)  $rose(CLK) );
  ap_sync_only_qn: assert property ( @(posedge QN or negedge QN) $rose(CLK) );

  // Coverage: exercise all control paths and data behaviors
  cv_set:            cover property ( S );
  cv_reset:          cover property ( !S && R );
  cv_sr_both:        cover property ( S && R );                // S dominates
  cv_hold:           cover property ( !S && !R && !D );
  cv_toggle_from0:   cover property ( (!S && !R && D && (Q==1'b0)) ##1 (Q==1'b1) );
  cv_toggle_from1:   cover property ( (!S && !R && D && (Q==1'b1)) ##1 (Q==1'b0) );
  // Coverage to reveal non-complement Q/QN behavior in toggle path
  cv_equal_outputs:  cover property ( (!S && !R && D) ##1 (Q==QN) );

endmodule

bind TFFSR TFFSR_sva sva_i (.*);