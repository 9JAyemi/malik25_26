// SVA for TLATNTSCAX2TS
module TLATNTSCAX2TS_sva (
  input logic E, SE, CK, ECK
);

  // Sample on any relevant edge (combinational behavior)
  default clocking cb @(
    posedge CK or negedge CK or
    posedge E  or negedge E  or
    posedge SE or negedge SE
  ); endclocking

  // Functional equivalence (4-state match)
  assert property (ECK === ((E & SE) ? CK : 1'b0));

  // No X on output when inputs are known + 2-state equivalence then
  assert property (!$isunknown({E,SE,CK}))
    |-> (!$isunknown(ECK) && (ECK == ((E & SE) ? CK : 1'b0)));

  // Basic gating behavior
  assert property (!(E & SE) |-> (ECK == 1'b0));
  assert property ( (E & SE) |-> (ECK == CK));

  // Edge sanity
  assert property ($rose(ECK) |-> (CK && (E & SE)));
  assert property ($fell(ECK) |-> ((!CK) || !(E & SE)));

  // Coverage: pass-through, blocked, and enable/disable while CK high
  cover property ($rose(CK) && (E & SE) && $rose(ECK));
  cover property ($fell(CK) && (E & SE) && $fell(ECK));
  cover property ($rose(CK) && !(E & SE) && (ECK == 1'b0));
  cover property ($rose(E & SE) && CK && $rose(ECK));
  cover property ($fell(E & SE) && CK && $fell(ECK));

endmodule

bind TLATNTSCAX2TS TLATNTSCAX2TS_sva i_TLATNTSCAX2TS_sva (.E(E), .SE(SE), .CK(CK), .ECK(ECK));