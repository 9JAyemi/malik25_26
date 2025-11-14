// SVA for image_filter_Block_proc
// Bind this module to the DUT
bind image_filter_Block_proc image_filter_Block_proc_sva();

module image_filter_Block_proc_sva;

  // convenience
  wire fire = (ap_sig_cseq_ST_st1_fsm_0 && !ap_sig_bdd_38);

  // Default clock
  default clocking cb @ (posedge ap_clk); endclocking

  // Reset effects (no disable)
  ap_rst_done_reg_reset: assert property (ap_rst |=> (ap_done_reg==1'b0));
  ap_rst_pregs_reset:    assert property (ap_rst |=> (ap_return_0_preg==12'h0 && ap_return_1_preg==12'h0 &&
                                                      ap_return_2_preg==12'h0 && ap_return_3_preg==12'h0));
  ap_rst_fsm_reset:      assert property (ap_rst |=> (ap_CS_fsm==ap_ST_st1_fsm_0));

  // Derived signal correctness
  bdd38_eq:   assert property (disable iff (ap_rst) ap_sig_bdd_38 == ((ap_start==1'b0) || (ap_done_reg==1'b1)));
  cseq_eq:    assert property (disable iff (ap_rst) ap_sig_cseq_ST_st1_fsm_0 == ap_sig_bdd_20);
  bdd20_eq:   assert property (disable iff (ap_rst) ap_sig_bdd_20 == (ap_CS_fsm==ap_ST_st1_fsm_0));

  // Idle/ready/done relations
  idle_eq:          assert property (disable iff (ap_rst) ap_idle == (~ap_start));
  ready_eq:         assert property (disable iff (ap_rst) ap_ready == fire);
  done_eq:          assert property (disable iff (ap_rst) ap_done  == (ap_done_reg || fire));
  ready_no_done_reg:assert property (disable iff (ap_rst) ap_ready |-> !ap_done_reg);
  ready_implies_start: assert property (disable iff (ap_rst) ap_ready |-> ap_start);
  idle_ready_mutex: assert property (disable iff (ap_rst) !(ap_idle && ap_ready));

  // ap_done_reg state machine
  done_clr_on_cont: assert property (disable iff (ap_rst) ap_continue |=> !ap_done_reg);
  done_set_on_fire: assert property (disable iff (ap_rst) (fire && !ap_continue) |=> ap_done_reg);
  done_hold:        assert property (disable iff (ap_rst) (!ap_continue && !fire) |=> $stable(ap_done_reg));

  // Return datapath
  ret_passthru_on_fire: assert property (disable iff (ap_rst)
    fire |-> (ap_return_0==rows[11:0] && ap_return_2==rows[11:0] &&
              ap_return_1==cols[11:0] && ap_return_3==cols[11:0]));

  ret_from_preg_when_no_fire: assert property (disable iff (ap_rst)
    (!fire) |-> (ap_return_0==ap_return_0_preg && ap_return_1==ap_return_1_preg &&
                 ap_return_2==ap_return_2_preg && ap_return_3==ap_return_3_preg));

  ret_capture_on_fire: assert property (disable iff (ap_rst)
    fire |=> (ap_return_0_preg==rows[11:0] && ap_return_2_preg==rows[11:0] &&
              ap_return_1_preg==cols[11:0] && ap_return_3_preg==cols[11:0]));

  ret_hold_when_no_fire: assert property (disable iff (ap_rst)
    (!fire) |=> ($stable(ap_return_0_preg) && $stable(ap_return_1_preg) &&
                 $stable(ap_return_2_preg) && $stable(ap_return_3_preg)));

  // No X on key signals after reset
  no_x_ctrl: assert property (disable iff (ap_rst)
    !$isunknown({ap_done, ap_ready, ap_idle, ap_done_reg,
                 ap_return_0, ap_return_1, ap_return_2, ap_return_3}));

  // Covers
  cover_fire:        cover property (disable iff (ap_rst) fire);
  cover_done_set:    cover property (disable iff (ap_rst) fire && !ap_continue ##1 ap_done_reg);
  cover_done_clear:  cover property (disable iff (ap_rst) ap_done_reg && ap_continue ##1 !ap_done_reg);
  cover_idle_ready:  cover property (disable iff (ap_rst) ~ap_start ##1 (ap_start && !ap_done_reg));

endmodule