// SVA for sky130_fd_sc_hd__or4

bind sky130_fd_sc_hd__or4 sky130_fd_sc_hd__or4_sva or4_sva();

module sky130_fd_sc_hd__or4_sva;

  default clocking cb @(*); endclocking

  // helpers
  let any1 = (A===1) || (B===1) || (C===1) || (D===1);
  let all0 = (A===0) && (B===0) && (C===0) && (D===0);
  let anyX = $isunknown(A) || $isunknown(B) || $isunknown(C) || $isunknown(D);
  let known = !anyX;

  // functional correctness (4-state, reactive)
  ap_func:      assert property (1 |-> ##0 (X === (A|B|C|D)));

  // helpful refinements
  ap_any1_one:  assert property (any1 |-> ##0 (X === 1'b1));
  ap_all0_zero: assert property (all0 |-> ##0 (X === 1'b0));
  ap_known_det: assert property (known |-> ##0 !$isunknown(X));
  ap_xprop:     assert property ((anyX && !any1) |-> ##0 $isunknown(X));

  // supplies must be correct
  ap_supplies:  assert property (VPWR===1'b1 && VPB===1'b1 && VGND===1'b0 && VNB===1'b0);

  // minimal but meaningful coverage
  cp_X0:        cover property (X===1'b0);
  cp_X1:        cover property (X===1'b1);
  cp_all0:      cover property (all0);
  cp_A_rise:    cover property (B===0 && C===0 && D===0 && $rose(A) && X===1);
  cp_B_rise:    cover property (A===0 && C===0 && D===0 && $rose(B) && X===1);
  cp_C_rise:    cover property (A===0 && B===0 && D===0 && $rose(C) && X===1);
  cp_D_rise:    cover property (A===0 && B===0 && C===0 && $rose(D) && X===1);
  cp_A_fall:    cover property (B===0 && C===0 && D===0 && $fell(A) && X===0);
  cp_B_fall:    cover property (A===0 && C===0 && D===0 && $fell(B) && X===0);
  cp_C_fall:    cover property (A===0 && B===0 && D===0 && $fell(C) && X===0);
  cp_D_fall:    cover property (A===0 && B===0 && C===0 && $fell(D) && X===0);
  cp_xprop:     cover property ((anyX && !any1) && $isunknown(X));

endmodule