// SVA for TLATNTSCAX2TS

module TLATNTSCAX2TS_sva (input logic E, SE, CK, ECK);

  default clocking cb @(posedge CK); endclocking

  bit past_valid;
  always @(posedge CK) past_valid <= 1'b1;

  // Functional correctness
  ap_se_sets1:        assert property (SE |-> ##0 (ECK == 1'b1));
  ap_e_sets0_nose:    assert property ((!SE && E) |-> ##0 (ECK == 1'b0));
  ap_hold_when_idle:  assert property (past_valid && !SE && !E |-> ##0 (ECK == $past(ECK)));
  ap_priority:        assert property ((SE && E) |-> ##0 (ECK == 1'b1)); // SE dominates

  // Change only with a cause; and output becomes known when updated
  ap_change_has_cause: assert property (past_valid && (ECK != $past(ECK)) |-> (SE || E));
  ap_known_on_update:  assert property ((SE || E) |-> ##0 !$isunknown(ECK));

  // Coverage
  cp_se_branch:        cover property (SE ##0 (ECK == 1'b1));
  cp_e_branch:         cover property ((!SE && E) ##0 (ECK == 1'b0));
  cp_hold_branch:      cover property (past_valid && !SE && !E ##0 (ECK == $past(ECK)));
  cp_both_high:        cover property ((SE && E) ##0 (ECK == 1'b1));
  cp_eck_rise:         cover property ($rose(ECK));
  cp_eck_fall:         cover property ($fell(ECK));

endmodule

bind TLATNTSCAX2TS TLATNTSCAX2TS_sva sva_i (.*);