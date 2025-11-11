// SVA for dlp_reg
// Bind this file: bind dlp_reg dlp_reg_sva;

module dlp_reg_sva;

  default clocking cb @(posedge hb_clk); endclocking

  // Basic signal equivalences
  ap_fmt_map:     assert property (hb_fmt == hb_cntrl_w2[1]);
  ap_sen_map:     assert property (hb_sen == hb_cntrl_w2[2]);
  ap_stp_map:     assert property (hb_stp == hb_cntrl_w2[3]);
  ap_wc_map:      assert property (hb_wc  == wc2);
  ap_wcf_map:     assert property (wcf    == adr_cntrl2[0]);
  ap_nextstp_map: assert property (next_stp == hb_cntrl_w2[3]);
  ap_idle_eq:     assert property (dl_idle == ((hb_addr == hb_end) || dl_idle_hold));

  // Remainder pipeline and dlp_wcnt calculation
  ap_remainder_pipe: assert property (disable iff (!hb_rstn || dlp_rstn_hb)
                                      remainder == $past(hb_end) - $past(hb_addr));
  ap_wcnt_sat:       assert property (disable iff (!hb_rstn) (remainder > 29'd8) |-> dlp_wcnt == 5'd7);
  ap_wcnt_small:     assert property (disable iff (!hb_rstn) (remainder inside {[29'd1:29'd8]})
                                      |-> dlp_wcnt == (remainder[4:0] - 5'd1));
  ap_wcnt_bound:     assert property (disable iff (!hb_rstn) dlp_wcnt <= 5'd7);

  // Address/control loading and sequencing
  ap_start_set:         assert property (disable iff (!hb_rstn || dlp_rstn_hb)
                                         start_strobe_comb |=> start_strobe);
  ap_hold_set:          assert property (disable iff (!hb_rstn || dlp_rstn_hb)
                                         ((dlp_hb_w && !hb_adr[2]) || (dlp_de_w && !de_adr[2])) |=> hold_start);
  ap_start_loads_addr:  assert property (disable iff (!hb_rstn || dlp_rstn_hb)
                                         (start_strobe && dl_idle)
                                         |=> (hb_addr == $past(hb_addr1) &&
                                              adr_cntrl2 == $past(adr_cntrl1) &&
                                              wc2 == $past(wc1) &&
                                              !hold_start && !start_strobe));
  ap_addr_inc:          assert property (disable iff (!hb_rstn)
                                         (next_dle && !dl_idle) |=> hb_addr == $past(hb_addr) + 28'h1);
  ap_load_end_on_cmd:   assert property (disable iff (!hb_rstn || dlp_rstn_hb)
                                         (dl_cmd_strb && !hold_start)
                                         |=> (hb_end == $past(hb_end1) &&
                                              hb_cntrl_w2 == $past(hb_cntrl_w1)));
  ap_idle_forces_stp:   assert property (disable iff (!hb_rstn || dlp_rstn_hb)
                                         (dl_idle && !start_strobe) |=> hb_cntrl_w2[3]);
  ap_stop_list_jump:    assert property (disable iff (!hb_rstn || dlp_rstn_hb)
                                         (dl_cmd_strb && !hold_start && stop_list && !dl_idle)
                                         |=> hb_addr == ($past(hb_end1) - 28'h1));

  // dl_idle_hold behavior
  ap_idle_hold_set:     assert property (disable iff (!hb_rstn)
                                         (hb_stp || dl_idle) |=> dl_idle_hold);
  ap_idle_hold_clr:     assert property (disable iff (!hb_rstn)
                                         (dl_cmd_strb && !hold_start) |=> !dl_idle_hold);
  ap_idle_when_equal:   assert property (disable iff (!hb_rstn)
                                         (hb_addr == hb_end) |-> dl_idle);

  // cmd_rdy_ld protocol
  ap_cmd_set:    assert property (disable iff (!hb_rstn || dlp_rstn_hb)
                                  (dl_cmd_strb || (start_strobe && dl_idle)) |=> cmd_rdy_ld);
  ap_cmd_sticky: assert property (disable iff (!hb_rstn || dlp_rstn_hb)
                                  (cmd_rdy_ld && !cmd_ack) |=> cmd_rdy_ld);
  ap_cmd_ack_clr:assert property (disable iff (!hb_rstn)
                                  cmd_ack |=> !cmd_rdy_ld);
  ap_cmd_rst_clr:assert property (disable iff (!hb_rstn) dlp_rstn_hb |=> !cmd_rdy_ld);

  // adr_cntrl2[0] clear on reset_wait
  ap_wcf_clear_on_reset_wait: assert property (disable iff (!hb_rstn)
                                               reset_wait |=> !adr_cntrl2[0]);

  // dlp_actv_2 control
  ap_actv_set_cmd:    assert property (disable iff (!hb_rstn || dlp_rstn_hb)
                                       (dl_cmd_strb && !hb_cntrl_w1[3]) |=> dlp_actv_2);
  ap_actv_set_toggle: assert property (disable iff (!hb_rstn || dlp_rstn_hb)
                                       (dl_idle && !next_stp) |=> dlp_actv_2);
  ap_actv_clr_idle:   assert property (disable iff (!hb_rstn || dlp_rstn_hb)
                                       (!actv_stp && dl_idle && next_stp) |=> !dlp_actv_2);
  ap_actv_clr_cmd:    assert property (disable iff (!hb_rstn || dlp_rstn_hb)
                                       (dl_cmd_strb && hb_cntrl_w1[3]) |=> !dlp_actv_2);

  // Safety: forward progress implies non-negative remainder while active
  ap_remainder_nonneg_when_active: assert property (disable iff (!hb_rstn)
                                                    !dl_idle |-> (hb_end >= hb_addr));

  // Coverage
  cp_hb_write_path:     cover property (dlp_hb_w && !hb_adr[2] ##1 dlp_hb_w && hb_adr[2] ##1 dl_cmd_strb);
  cp_de_write_path:     cover property (dlp_de_w && !de_adr[2] ##1 dlp_de_w && de_adr[2] ##1 dl_cmd_strb);
  cp_start_to_load:     cover property (start_strobe_comb ##1 (start_strobe && dl_idle)
                                        ##1 (hb_addr == hb_addr1));
  cp_addr_run_then_idle: cover property ((start_strobe && dl_idle) ##1 (!dl_idle && next_dle)[*3]
                                         ##1 (hb_addr == hb_end) ##1 dl_idle);
  cp_stop_list_jump:    cover property (dl_cmd_strb && !hold_start && stop_list && !dl_idle
                                        ##1 hb_addr == $past(hb_end1) - 28'h1);
  cp_wcnt_saturate:     cover property (remainder > 29'd8 && dlp_wcnt == 5'd7);
  cp_wcnt_exact:        cover property (remainder == 29'd1 && dlp_wcnt == 5'd0);
  cp_actv_cycle:        cover property ((dl_cmd_strb && !hb_cntrl_w1[3]) ##1 dlp_actv_2
                                        ##[1:8] (!actv_stp && dl_idle && next_stp) ##1 !dlp_actv_2);
  cp_wcf_reset:         cover property (reset_wait ##1 !wcf);

endmodule

bind dlp_reg dlp_reg_sva;