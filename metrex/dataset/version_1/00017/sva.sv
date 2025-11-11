// SVA for myDFF: concise, high-quality checks and coverage
// Bind these assertions to the DUT

module myDFF_sva (input logic CK, D, RN, SN, Q, QN);

  default clocking cb @(posedge CK); endclocking

  // Enable checks after the first sampled edge
  logic started;
  initial started = 0;
  always @(posedge CK) started <= 1;

  // Functional correctness: Q equals function of previous-cycle controls/data
  a_func_update: assert property (cb
    started |-> Q == ( $past(RN) ? 1'b0 : ($past(SN) ? 1'b1 : $past(D)) )
  );

  // Priority when both RN and SN are 1: reset dominates set
  a_priority: assert property (cb
    started && $past(RN) && $past(SN) |-> Q == 1'b0
  );

  // Q only changes on a rising CK edge (no glitches between clocks)
  a_q_changes_only_on_clk: assert property (
    $changed(Q) |-> $rose(CK)
  );

  // Complementary output must always match
  a_qn_is_complement: assert property (
    QN === ~Q
  );

  // No X on Q after first update; controls/data used are known
  a_no_x_q: assert property (cb
    started |-> !$isunknown(Q)
  );
  a_no_x_ctrl_data: assert property (cb
    started |-> !$isunknown({$past(RN), $past(SN), $past(D)})
  );

  // Coverage: exercise each path and key transitions
  c_reset_path:  cover property (cb started && $past(RN) && !$past(SN) && Q==1'b0);
  c_set_path:    cover property (cb started && !$past(RN) && $past(SN) && Q==1'b1);
  c_both_high:   cover property (cb started && $past(RN) && $past(SN) && Q==1'b0);
  c_data_0_to_1: cover property (cb started && !$past(RN) && !$past(SN) &&
                                 $past(Q)==1'b0 && $past(D)==1'b1 && Q==1'b1);
  c_data_1_to_0: cover property (cb started && !$past(RN) && !$past(SN) &&
                                 $past(Q)==1'b1 && $past(D)==1'b0 && Q==1'b0);

endmodule

bind myDFF myDFF_sva sva_inst (.CK(CK), .D(D), .RN(RN), .SN(SN), .Q(Q), .QN(QN));