// SVA for negate: MO = (S==1) ? ~B : ~A
module negate_sva (input logic A, B, S, MO);
  // Re-evaluate on any input edge
  default clocking cb @ (posedge A or negedge A or posedge B or negedge B or posedge S or negedge S); endclocking

  // Core functionality
  ap_sel1: assert property (S === 1 |-> MO === ~B);
  ap_sel0: assert property (S === 0 |-> MO === ~A);

  // X/Z handling (4-state correctness)
  ap_xsel: assert property ($isunknown(S) |-> ((~A === ~B) ? (MO === ~A) : $isunknown(MO)));
  ap_xB:   assert property ((S === 1) && $isunknown(B) |-> $isunknown(MO));
  ap_xA:   assert property ((S === 0) && $isunknown(A) |-> $isunknown(MO));

  // No dependence on unselected input (no spurious glitches)
  ap_no_dep_from_B_when_selA: assert property (S === 0 && $stable(A) && $stable(S) |=> $stable(MO));
  ap_no_dep_from_A_when_selB: assert property (S === 1 && $stable(B) && $stable(S) |=> $stable(MO));

  // Coverage
  cp_sel0:   cover property (S === 0 && !$isunknown(A) && MO === ~A);
  cp_sel1:   cover property (S === 1 && !$isunknown(B) && MO === ~B);
  cp_toggle: cover property (S === 0 ##1 S === 1 ##1 S === 0);
  cp_xmerge: cover property ($isunknown(S) && (~A === ~B) && (MO === ~A));
  cp_xmux:   cover property ($isunknown(S) && (~A !== ~B) && $isunknown(MO));
endmodule

bind negate negate_sva u_negate_sva (.*);