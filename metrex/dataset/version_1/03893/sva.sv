// SVA for JK_FF
module jk_ff_sva (input J, K, C, R, E, input Q, Qn);

  default clocking cb @(posedge C); endclocking

  // helper for $past
  bit past_v;
  initial past_v = 0;
  always @(posedge C) past_v <= 1'b1;

  // Inputs/outputs known at clock edge
  assert property ( !$isunknown({J,K,E,R}) );
  assert property ( !$isunknown({Q,Qn}) );

  // Qn is always the complement of Q (checked on clock and any output change)
  assert property (@(posedge C or posedge Q or negedge Q or posedge Qn or negedge Qn) Qn == ~Q);

  // Outputs only change synchronously on clock posedge
  assert property (@(posedge Q  or negedge Q ) $rose(C));
  assert property (@(posedge Qn or negedge Qn) $rose(C));

  // Priority/functional behavior (synchronous; check next-cycle state)
  // E low clears (dominates everything)
  assert property ( disable iff(!past_v) E==1'b0 |=> (Q==1'b0 && Qn==1'b1) );

  // R low clears when enabled
  assert property ( disable iff(!past_v) (E==1'b1 && R==1'b0) |=> (Q==1'b0 && Qn==1'b1) );

  // JK behavior when enabled and not in reset
  // Toggle
  assert property ( disable iff(!past_v) (E && R && J && K) |=> (Q == ~$past(Q) && Qn == ~$past(Qn)) );
  // Set
  assert property ( disable iff(!past_v) (E && R && J && !K) |=> (Q==1'b1 && Qn==1'b0) );
  // Reset
  assert property ( disable iff(!past_v) (E && R && !J && K) |=> (Q==1'b0 && Qn==1'b1) );
  // Hold
  assert property ( disable iff(!past_v) (E && R && !J && !K) |=> (Q==$past(Q) && Qn==$past(Qn)) );

  // Functional coverage
  cover property ( E==1'b0 ##1 (Q==0 && Qn==1) );
  cover property ( E && !R ##1 (Q==0 && Qn==1) );
  cover property ( E && R && J && K    ##1 (Q != $past(Q)) );
  cover property ( E && R && J && !K   ##1 (Q==1) );
  cover property ( E && R && !J && K   ##1 (Q==0) );
  cover property ( E && R && !J && !K  ##1 (Q==$past(Q)) );

endmodule

bind JK_FF jk_ff_sva u_jk_ff_sva(.*);