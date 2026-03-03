// SVA for sky130_fd_sc_hvl__lsbuflv2hv_clkiso_hlkg
// Bindable, references internal nets for thorough checking.

module sky130_fd_sc_hvl__lsbuflv2hv_clkiso_hlkg_sva;

  // Functional spec: pure comb X = SLEEP_B & A
  ap_func:    assert property (@(A or SLEEP_B or X))
                 X === (SLEEP_B & A);

  // Gating behavior
  ap_g0:      assert property (@(A or SLEEP_B or X))
                 !SLEEP_B |-> (X === 1'b0);
  ap_g1:      assert property (@(A or SLEEP_B or X))
                 SLEEP_B |-> (X === A);

  // Internal net consistency
  ap_sleep:   assert property (@(SLEEP_B or SLEEP))
                 SLEEP === ~SLEEP_B;
  ap_and:     assert property (@(A or SLEEP_B or and0_out_X))
                 and0_out_X === (SLEEP_B & A);
  ap_buf:     assert property (@(X or and0_out_X))
                 X === and0_out_X;

  // No spurious output changes
  ap_no_spur: assert property (@(A or SLEEP_B or X))
                 $changed(X) |-> ($changed(A) || $changed(SLEEP_B));

  // Known-propagation when inputs known
  ap_known:   assert property (@(A or SLEEP_B or X))
                 (!$isunknown({SLEEP_B, A})) |-> !$isunknown(X);

  // Power pins are tied correctly (should always hold)
  ap_pwr:     assert property (@(VPWR or VGND or LVPWR or VPB or VNB))
                 (VPWR===1'b1) && (LVPWR===1'b1) && (VPB===1'b1) &&
                 (VGND===1'b0) && (VNB===1'b0);

  // Coverage: all operating points and key transitions
  cp_all_00:  cover property (@(A or SLEEP_B)) (!SLEEP_B && (A==0) && (X==0));
  cp_all_01:  cover property (@(A or SLEEP_B)) (!SLEEP_B && (A==1) && (X==0));
  cp_all_10:  cover property (@(A or SLEEP_B)) ( SLEEP_B && (A==0) && (X==0));
  cp_all_11:  cover property (@(A or SLEEP_B)) ( SLEEP_B && (A==1) && (X==1));

  cp_a_up:    cover property (@(posedge A))  SLEEP_B && X;
  cp_a_dn:    cover property (@(negedge A))  SLEEP_B && !X;
  cp_iso_lo:  cover property (@(negedge SLEEP_B)) X==1'b0;
  cp_iso_hi:  cover property (@(posedge SLEEP_B)) X==A;

endmodule

bind sky130_fd_sc_hvl__lsbuflv2hv_clkiso_hlkg sky130_fd_sc_hvl__lsbuflv2hv_clkiso_hlkg_sva sva_i();