// SVA for mig_7series_v2_3_ddr_phy_ocd_mux
// Bind into DUT
bind mig_7series_v2_3_ddr_phy_ocd_mux mig_7series_v2_3_ddr_phy_ocd_mux_sva #(
  .DQS_CNT_WIDTH(DQS_CNT_WIDTH),
  .DQS_WIDTH    (DQS_WIDTH)
) mig_7series_v2_3_ddr_phy_ocd_mux_sva_i();

module mig_7series_v2_3_ddr_phy_ocd_mux_sva #(
  parameter int DQS_CNT_WIDTH = 3,
  parameter int DQS_WIDTH     = 8
) ();

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Simple combinational relationships
  ap_ktap_left:  assert property (ktap_at_left_edge      == ocd_ktap_left);
  ap_ktap_right: assert property (ktap_at_right_edge     == (lim2poc_ktap_right || ocd_ktap_right));
  ap_mmcm_rdy:   assert property (mmcm_edge_detect_rdy   == (lim2poc_rdy || ocd_edge_detect_rdy));
  ap_prech_or:   assert property (oclk_prech_req         == (ocd_prech_req || lim2init_prech_req));

  // Tied-off outputs
  ap_stg3_tied_off: assert property (!po_stg3_incdec && !po_en_stg3);

  // setup_po definition
  ap_setup_po_def: assert property (
    setup_po == (lim2stg2_inc || lim2stg2_dec || lim2stg3_inc || lim2stg3_dec ||
                 ocd2stg2_inc || ocd2stg2_dec || ocd2stg3_inc || ocd2stg3_dec ||
                 ocd_cntlr2stg2_dec)
  );

  // po_setup_r FSM: load to 2'b11 on setup, then count down to 0
  ap_setup_po_load:  assert property (setup_po                        |=> po_setup_r == 2'b11);
  ap_setup_po_count: assert property (!setup_po && (po_setup_r != 0)  |=> po_setup_r == $past(po_setup_r) - 2'b01);
  ap_setup_po_hold0: assert property (!setup_po && (po_setup_r == 0)  |=> po_setup_r == 0);

  // po_en_stg23: one-cycle pulse when po_setup_r == 2'b01
  ap_en_stg23_when:     assert property ((po_setup_r == 2'b01) |=> po_en_stg23);
  ap_en_stg23_only_then:assert property (po_en_stg23 |-> $past(po_setup_r) == 2'b01);

  // po_wait counter: load to PO_WAIT-1 (=14), then decrement to 0
  ap_wait_load:      assert property (po_en_stg23                        |=> po_wait_r == 14);
  ap_wait_count:     assert property (!po_en_stg23 && (po_wait_r != 0)   |=> po_wait_r == $past(po_wait_r) - 1);
  ap_wait_hold_zero: assert property (!po_en_stg23 && (po_wait_r == 0)   |=> po_wait_r == 0);

  // po_stg23_sel behavior
  ap_sel_on_setup:           assert property (setup_po                                |=> po_stg23_sel == sel_stg3);
  ap_sel_hold_while_wait:    assert property (!setup_po && po_stg23_sel && (po_wait_r != 1) |=> po_stg23_sel);
  ap_sel_drop_one_before_0:  assert property (!setup_po && (po_wait_r == 1)          |=> !po_stg23_sel);

  // po_stg23_incdec behavior
  ap_incdec_on_setup: assert property (setup_po |=> po_stg23_incdec == po_inc);
  ap_incdec_hold:     assert property (!setup_po |=> po_stg23_incdec == $past(po_stg23_incdec));

  // po_rdy is registered "not busy" (uses po_wait_ns combinational next-state)
  ap_rdy_registered: assert property (po_rdy == $past(!(setup_po || (po_setup_r != 0) || (po_wait_ns != 0))));

  // Shift/select correctness
  ap_shift_exact: assert property (wl_po_fine_cnt_sel == wl_po_fine_shifted[5:0]);
  ap_shift_zero_out_of_range: assert property ((oclkdelay_calib_cnt >= DQS_WIDTH) |-> (wl_po_fine_cnt_sel == 6'b0));

  // Concise functional coverage
  cp_stg2_path: cover property (
    setup_po && !sel_stg3 ##1 po_en_stg23 ##1 (po_wait_r == 14)
    ##[1:$] (po_wait_r == 1) ##1 !po_stg23_sel ##1 po_rdy
  );

  cp_stg3_path_inc: cover property (
    setup_po && sel_stg3 &&  po_inc ##1 po_en_stg23 ##1 po_stg23_sel
    ##[1:$] (po_wait_r == 1) ##1 !po_stg23_sel ##1 po_rdy
  );

  cp_stg3_path_dec: cover property (
    setup_po && sel_stg3 && !po_inc ##1 po_en_stg23 ##1 po_stg23_sel
    ##[1:$] (po_wait_r == 1) ##1 !po_stg23_sel ##1 po_rdy
  );

  cp_prech_req: cover property ($rose(ocd_prech_req) or $rose(lim2init_prech_req));

endmodule