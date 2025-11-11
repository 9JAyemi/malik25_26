// SVA for bmu: bm must equal {cx1,cx0}, no spurious changes, full code/toggle coverage

module bmu_sva (input logic cx0, cx1, input logic [1:0] bm);
  // Sample on any input edge; use ##0 to check post-update in same timestep
  clocking cb @(posedge cx0 or negedge cx0 or posedge cx1 or negedge cx1); endclocking
  default clocking cb;

  // Functional equivalence (also flags X on bm when inputs are known)
  assert property (disable iff ($isunknown({cx1,cx0}))
                   1'b1 |-> ##0 (bm == {cx1,cx0}))
    else $error("BMU: bm must equal {cx1,cx0}");

  // Bit-independence on single-input toggles
  assert property (disable iff ($isunknown({cx1,cx0,bm}))
                   ($changed(cx0) && !$changed(cx1)) |-> ##0 ($changed(bm[0]) && !$changed(bm[1])))
    else $error("BMU: bm[0] must track cx0; bm[1] must hold when only cx0 changes");

  assert property (disable iff ($isunknown({cx1,cx0,bm}))
                   ($changed(cx1) && !$changed(cx0)) |-> ##0 ($changed(bm[1]) && !$changed(bm[0])))
    else $error("BMU: bm[1] must track cx1; bm[0] must hold when only cx1 changes");

  // Both inputs toggling implies both output bits toggle
  assert property (disable iff ($isunknown({cx1,cx0,bm}))
                   ($changed(cx0) && $changed(cx1)) |-> ##0 ($changed(bm[1]) && $changed(bm[0])))
    else $error("BMU: both bm bits should toggle when both inputs toggle");

  // No spurious bm change without an input change
  assert property (@(posedge bm[0] or negedge bm[0] or posedge bm[1] or negedge bm[1])
                   disable iff ($isunknown({cx1,cx0,bm}))
                   ($changed(cx0) || $changed(cx1)))
    else $error("BMU: bm changed without an input change");

  // Coverage: all input/output codes observed
  cover property (1'b1 |-> ##0 ({cx1,cx0} == 2'b00 && bm == 2'b00));
  cover property (1'b1 |-> ##0 ({cx1,cx0} == 2'b01 && bm == 2'b01));
  cover property (1'b1 |-> ##0 ({cx1,cx0} == 2'b10 && bm == 2'b10));
  cover property (1'b1 |-> ##0 ({cx1,cx0} == 2'b11 && bm == 2'b11));

  // Coverage: single and simultaneous toggles and corresponding bm reactions
  cover property (($changed(cx0) && !$changed(cx1)) ##0 $changed(bm[0]));
  cover property (($changed(cx1) && !$changed(cx0)) ##0 $changed(bm[1]));
  cover property (($changed(cx0) && $changed(cx1)) ##0 ($changed(bm[0]) && $changed(bm[1])));
endmodule

bind bmu bmu_sva bmu_sva_i(.cx0(cx0), .cx1(cx1), .bm(bm));