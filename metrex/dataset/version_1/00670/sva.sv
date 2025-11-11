// SVA for dff_sr: concise, high-quality checks and coverage
module dff_sr_sva (input logic CK, D, S, R, Q, QN);

  default clocking cb @(posedge CK); endclocking

  // Functional correctness per spec
  a_set      : assert property ( S                |=> Q == 1'b1 );
  a_reset    : assert property ( !S && R          |=> Q == 1'b0 );
  a_data     : assert property ( !S && !R         |=> Q == $past(D) );
  a_priority : assert property ( S && R           |=> Q == 1'b1 ); // S dominates R

  // Complementary outputs
  a_qn_comp  : assert property ( QN === ~Q );

  // No glitches between clock edges (Q updates only on posedge CK)
  a_stable_negedge : assert property (@(negedge CK) $stable(Q));

  // Knownness when inputs are determinative
  a_known_next : assert property ( (S || R || (!S && !R && !$isunknown(D))) |=> !$isunknown(Q) );
  a_qn_known   : assert property ( !$isunknown(Q) |-> !$isunknown(QN) );

  // Coverage: exercise all behaviors
  c_set        : cover property ( S                |=> Q == 1'b1 );
  c_reset      : cover property ( !S && R          |=> Q == 1'b0 );
  c_data_rise  : cover property ( !S && !R && $rose(D) |=> Q == 1'b1 );
  c_data_fall  : cover property ( !S && !R && $fell(D) |=> Q == 1'b0 );
  c_both_sr    : cover property ( S && R           |=> Q == 1'b1 );
  c_qn_toggle  : cover property ( (Q != $past(Q)) && (QN != $past(QN)) && (QN === ~Q) );

endmodule

// Bind into DUT
bind dff_sr dff_sr_sva u_dff_sr_sva (.CK(CK), .D(D), .S(S), .R(R), .Q(Q), .QN(QN));