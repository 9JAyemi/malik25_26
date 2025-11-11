// SVA checker for mux2to1 with internal connectivity; bind into DUT
module mux2to1_sva (
    input A0,
    input A1,
    input S,
    input Y,
    input VPWR,
    input VGND,
    input VPB,
    input VNB,
    // internal nets
    input not_S,
    input A0_and_not_S,
    input A1_and_S,
    input Y_buf
);

  // Sample on any relevant edge
  default clocking cb @(
      posedge A0 or negedge A0 or
      posedge A1 or negedge A1 or
      posedge S  or negedge S  or
      posedge Y  or negedge Y  or
      posedge VPWR or negedge VPWR or
      posedge VGND or negedge VGND
  ); endclocking

  // Reusable predicates
  let pwr_good   = (VPWR === 1'b1) && (VGND === 1'b0) && (VPB === VPWR) && (VNB === VGND);
  let in_known   = !$isunknown({A0,A1,S});
  let all_known  = !$isunknown({A0,A1,S,Y});

  // Power/body ties
  ap_pwr_ties: assert property (!$isunknown({VPWR,VGND,VPB,VNB}) |-> (VPB == VPWR && VNB == VGND));

  // Functional correctness (selected input drives Y)
  ap_func:      assert property (disable iff (!pwr_good || !in_known) Y === (S ? A1 : A0));
  ap_no_x_out:  assert property (disable iff (!pwr_good || !in_known) !$isunknown(Y));

  // Structural internal net checks
  ap_not:       assert property (disable iff (!pwr_good) !$isunknown(S)          |-> not_S         === ~S);
  ap_and0:      assert property (disable iff (!pwr_good) !$isunknown({A0,S})     |-> A0_and_not_S  === (A0 & ~S));
  ap_and1:      assert property (disable iff (!pwr_good) !$isunknown({A1,S})     |-> A1_and_S      === (A1 &  S));
  ap_or:        assert property (disable iff (!pwr_good) !$isunknown({A0_and_not_S,A1_and_S})
                                                                       |-> Y_buf         === (A0_and_not_S | A1_and_S));
  ap_buf:       assert property (disable iff (!pwr_good) !$isunknown(Y_buf)      |-> Y             === Y_buf);

  // Masking: inactive data input must not affect Y
  ap_mask_a1:   assert property (disable iff (!pwr_good || $isunknown({S,A0,A1}))
                                 (S==1'b0 && $changed(A1) && $stable(A0)) |-> $stable(Y));
  ap_mask_a0:   assert property (disable iff (!pwr_good || $isunknown({S,A0,A1}))
                                 (S==1'b1 && $changed(A0) && $stable(A1)) |-> $stable(Y));

  // Coverage: exercise both data legs and select behavior
  cp_leg0:      cover property (pwr_good && S==1'b0 && $changed(A0));
  cp_leg1:      cover property (pwr_good && S==1'b1 && $changed(A1));
  cp_sel_diff:  cover property (pwr_good && !$isunknown({A0,A1}) && (A0!=A1) && $changed(S));
  cp_sel_same:  cover property (pwr_good && !$isunknown({A0,A1}) && (A0==A1) && $changed(S));

endmodule

// Bind into the DUT to access internal nets by name
bind mux2to1 mux2to1_sva mux2to1_sva_i (.*);