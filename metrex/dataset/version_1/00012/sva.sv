// SVA for SNPS_CLOCK_GATE_HIGH_RegisterAdd_W24 and TLATNTSCAX2TS
// Function implemented: ENCLK/ECK == CLK/CK & EN/E & TE/SE

// Leaf cell SVA
module TLATNTSCAX2TS_sva (input logic E, SE, CK, ECK);
  default clocking cb @(posedge CK or negedge CK or posedge E or negedge E or posedge SE or negedge SE); endclocking

  // Functional equivalence
  assert property (ECK == (E & SE & CK));

  // Edge sanity
  assert property (@(posedge ECK) (CK && E && SE));
  assert property (@(negedge ECK) (!CK || !E || !SE));

  // When gate open, output follows CK
  assert property (@(posedge CK) (E && SE) |-> ECK);
  assert property (@(negedge CK) (E && SE) |-> !ECK);

  // When gate closed, output held low
  assert property ((!E || !SE) |-> !ECK);

  // 4-state robustness
  assert property (!$isunknown({E,SE,CK}) |-> !$isunknown(ECK));

  // Coverage: all cause types for ECK edges
  cover property (@(posedge CK)  E && SE && ECK);      // rise via CK
  cover property (@(negedge CK)  E && SE && !ECK);     // fall via CK
  cover property (@(posedge E)   SE && CK && ECK);     // rise via E
  cover property (@(negedge E)   SE && CK && !ECK);    // fall via E
  cover property (@(posedge SE)  E && CK && ECK);      // rise via SE
  cover property (@(negedge SE)  E && CK && !ECK);     // fall via SE
  cover property (@(posedge CK) !(E && SE) && !ECK);   // gated off at CK edge
  cover property (@(negedge CK) !(E && SE) && !ECK);   // gated off at CK edge
endmodule

bind TLATNTSCAX2TS TLATNTSCAX2TS_sva(.E(E), .SE(SE), .CK(CK), .ECK(ECK));


// Top clock-gate wrapper SVA
module SNPS_CLOCK_GATE_HIGH_RegisterAdd_W24_sva (input logic CLK, EN, TE, ENCLK);
  default clocking cb @(posedge CLK or negedge CLK or posedge EN or negedge EN or posedge TE or negedge TE); endclocking

  // Functional equivalence
  assert property (ENCLK == (CLK & EN & TE));

  // Edge sanity
  assert property (@(posedge ENCLK) (CLK && EN && TE));
  assert property (@(negedge ENCLK) (!CLK || !EN || !TE));

  // When gate open, ENCLK follows CLK
  assert property (@(posedge CLK) (EN && TE) |-> ENCLK);
  assert property (@(negedge CLK) (EN && TE) |-> !ENCLK);

  // When gate closed, ENCLK held low
  assert property ((!EN || !TE) |-> !ENCLK);

  // 4-state robustness
  assert property (!$isunknown({CLK,EN,TE}) |-> !$isunknown(ENCLK));

  // Coverage: open/closed operation and all causes of ENCLK edges
  cover property (@(posedge CLK)  EN && TE && ENCLK);       // rise via CLK
  cover property (@(negedge CLK)  EN && TE && !ENCLK);      // fall via CLK
  cover property (@(posedge EN)   CLK && TE && ENCLK);      // rise via EN
  cover property (@(negedge EN)   CLK && TE && !ENCLK);     // fall via EN
  cover property (@(posedge TE)   CLK && EN && ENCLK);      // rise via TE
  cover property (@(negedge TE)   CLK && EN && !ENCLK);     // fall via TE
  cover property (@(posedge CLK) !(EN && TE) && !ENCLK);    // gated off at CLK edge
  cover property (@(negedge CLK) !(EN && TE) && !ENCLK);    // gated off at CLK edge
endmodule

bind SNPS_CLOCK_GATE_HIGH_RegisterAdd_W24 SNPS_CLOCK_GATE_HIGH_RegisterAdd_W24_sva(.CLK(CLK), .EN(EN), .TE(TE), .ENCLK(ENCLK));