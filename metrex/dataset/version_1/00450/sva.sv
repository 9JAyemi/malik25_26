// SVA for clock_gate/TLATNTSCAX2TS
// Concise, quality-focused checks and coverage

package clock_gate_sva;

  // Leaf-level checker (single source of truth)
  checker leaf_chk (input logic E, SE, CK, ECK);

    // Sample on any input edge; evaluate after updates (##0)
    default clocking cb @ (posedge E or negedge E or
                           posedge SE or negedge SE or
                           posedge CK or negedge CK); endclocking

    // Functional equivalence (4-state): ECK must be E & SE & CK
    assert property (1'b1 |-> ##0 (ECK === (E & SE & CK)));

    // Known propagation: if all inputs are known, output must be known
    assert property ((!$isunknown({E,SE,CK})) |-> ##0 (!$isunknown(ECK)));

    // Pass-through when enabled at CK edges
    assert property (@(posedge CK) (E && SE) |-> ##0 (ECK == 1'b1));
    assert property (@(negedge CK) (E && SE) |-> ##0 (ECK == 1'b0));

    // Blocked when disabled at CK edges
    assert property (@(posedge CK or negedge CK) (!E || !SE) |-> ##0 (ECK == 1'b0));

    // Minimal, targeted coverage: each input causing ECK rise/fall
    cover property (@(posedge CK)  (E && SE) ##0 (ECK == 1'b1)); // rise via CK
    cover property (@(posedge E)   (SE && CK) ##0 (ECK == 1'b1)); // rise via E
    cover property (@(posedge SE)  (E  && CK) ##0 (ECK == 1'b1)); // rise via SE

    cover property (@(negedge CK)  (E && SE) ##0 (ECK == 1'b0)); // fall via CK
    cover property (@(negedge E)   (SE && CK) ##0 (ECK == 1'b0)); // fall via E
    cover property (@(negedge SE)  (E  && CK) ##0 (ECK == 1'b0)); // fall via SE

    // Coverage: CK toggles while disabled, ECK held low
    cover property (@(posedge CK) (!E || !SE) ##0 (ECK == 1'b0));

  endchecker

  // Top-level wrapper checker to validate port connectivity
  checker top_chk (input logic CLK, EN, TE, ECK);
    default clocking cb @ (posedge CLK or negedge CLK or
                           posedge EN  or negedge EN  or
                           posedge TE  or negedge TE); endclocking
    assert property (1'b1 |-> ##0 (ECK === (EN & TE & CLK)));
  endchecker

  // Binds
  bind TLATNTSCAX2TS leaf_chk (.E(E), .SE(SE), .CK(CK), .ECK(ECK));
  bind clock_gate    top_chk  (.CLK(CLK), .EN(EN), .TE(TE), .ECK(ECK));

endpackage