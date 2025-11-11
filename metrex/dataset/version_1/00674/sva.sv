// SVA for TLATNTSCAX2TS: ECK must be E & SE; CK must not affect ECK.
// Bind this file to the DUT.
module TLATNTSCAX2TS_sva (input logic E, SE, CK, ECK);

  // Functional equivalence (4-state) checked on any relevant edge
  ap_func_and: assert property
    (@(posedge E or negedge E or posedge SE or negedge SE or posedge CK or negedge CK)
      ECK === (E & SE))
    else $error("ECK != (E & SE)");

  // CK independence: if E and SE are stable across a CK edge, ECK must be stable too
  ap_ck_indep: assert property
    (@(posedge CK or negedge CK)
      !$changed(E) && !$changed(SE) |-> !$changed(ECK))
    else $error("ECK changed on CK edge while E/SE stable");

  // 0-dominance and 1-mapping corner checks (4-state)
  ap_zero_dom_e:  assert property (@(posedge E or negedge E or posedge SE or negedge SE) (E  === 1'b0) |-> (ECK === 1'b0));
  ap_zero_dom_se: assert property (@(posedge E or negedge E or posedge SE or negedge SE) (SE === 1'b0) |-> (ECK === 1'b0));
  ap_one_map_e:   assert property (@(posedge E or negedge E or posedge SE or negedge SE) (E  === 1'b1) |-> (ECK === SE));
  ap_one_map_se:  assert property (@(posedge E or negedge E or posedge SE or negedge SE) (SE === 1'b1) |-> (ECK === E));

  // Knownness: if inputs are known, output must be known (no X/Z)
  ap_known: assert property
    (@(posedge E or negedge E or posedge SE or negedge SE or posedge CK or negedge CK)
      (!$isunknown(E) && !$isunknown(SE)) |-> !$isunknown(ECK))
    else $error("ECK is unknown while E and SE are known");

  // Coverage: exercise all input combos and ECK edges
  cv_e0_se0: cover property (@(posedge E or posedge SE or posedge CK or negedge E or negedge SE or negedge CK)
                              (E===1'b0 && SE===1'b0 && ECK===1'b0));
  cv_e0_se1: cover property (@(posedge E or posedge SE or posedge CK or negedge E or negedge SE or negedge CK)
                              (E===1'b0 && SE===1'b1 && ECK===1'b0));
  cv_e1_se0: cover property (@(posedge E or posedge SE or posedge CK or negedge E or negedge SE or negedge CK)
                              (E===1'b1 && SE===1'b0 && ECK===1'b0));
  cv_e1_se1: cover property (@(posedge E or posedge SE or posedge CK or negedge E or negedge SE or negedge CK)
                              (E===1'b1 && SE===1'b1 && ECK===1'b1));

  cv_eck_rise: cover property (@(posedge E or negedge E or posedge SE or negedge SE) $rose(ECK));
  cv_eck_fall: cover property (@(posedge E or negedge E or posedge SE or negedge SE) $fell(ECK));

endmodule

bind TLATNTSCAX2TS TLATNTSCAX2TS_sva (.E(E), .SE(SE), .CK(CK), .ECK(ECK));