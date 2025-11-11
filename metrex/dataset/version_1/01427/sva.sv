// SVA for sky130_fd_sc_lp__and2
// Bind into the DUT; no DUT edits needed.
`ifndef SKY130_FD_SC_LP__AND2_SVA
`define SKY130_FD_SC_LP__AND2_SVA

module sky130_fd_sc_lp__and2_sva;

  // Sample on any relevant pin change
  default clocking cb @(
      posedge A or negedge A or
      posedge B or negedge B or
      posedge VPWR or negedge VPWR or
      posedge VGND or negedge VGND or
      posedge VPB  or negedge VPB  or
      posedge VNB  or negedge VNB
  ); endclocking

  // Power-good definition (4-state aware)
  let pg = (VPWR===1'b1 && VGND===1'b0 && VPB===1'b1 && VNB===1'b0);

  // Functional correctness (AND and buffer)
  a_func_and:          assert property (pg |-> (X === (A & B)));
  a_and_internal:      assert property (pg |-> (and0_out_X === (A & B)));
  a_buf_connectivity:  assert property (pg |-> (X === and0_out_X));

  // No X/Z on outputs when inputs and power are known-good
  a_no_unknown_out:    assert property (pg && !$isunknown({A,B}) |-> !$isunknown({and0_out_X, X}));

  // Zero-delay response on input changes under power-good
  a_zero_delay:        assert property (pg && ($changed(A) || $changed(B))
                                        |-> (X === (A & B) && X === and0_out_X));

  // Output changes only if inputs or power/well pins change
  a_change_has_cause:  assert property (pg && $changed(X)
                                        |-> ($changed(A) || $changed(B) ||
                                             $changed(VPWR) || $changed(VGND) ||
                                             $changed(VPB)  || $changed(VNB)));

  // Well/body ties consistent with supplies when all known
  a_body_tied:         assert property (!$isunknown({VPWR,VGND,VPB,VNB})
                                        |-> (VPB === VPWR && VNB === VGND));

  // Functional coverage (under power-good)
  c_00:  cover property (pg && A==1'b0 && B==1'b0 && X==1'b0);
  c_01:  cover property (pg && A==1'b0 && B==1'b1 && X==1'b0);
  c_10:  cover property (pg && A==1'b1 && B==1'b0 && X==1'b0);
  c_11:  cover property (pg && A==1'b1 && B==1'b1 && X==1'b1);

  c_x_rise: cover property (pg && $rose(X));
  c_x_fall: cover property (pg && $fell(X));

  // Power-up behavior coverage
  c_pu_11: cover property ($rose(pg) && A==1'b1 && B==1'b1 && X==1'b1);
  c_pu_00: cover property ($rose(pg) && A==1'b0 && B==1'b0 && X==1'b0);

endmodule

// Bind to all instances of the cell
bind sky130_fd_sc_lp__and2 sky130_fd_sc_lp__and2_sva and2_sva_i();

`endif