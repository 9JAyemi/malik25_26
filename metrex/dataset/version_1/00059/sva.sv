// SVA for des_smline_3d
// Bind into DUT scope so we can reference internals
bind des_smline_3d des_smline_3d_sva();

module des_smline_3d_sva;

  default clocking cb @(posedge de_clk); endclocking
  default disable iff (!de_rstn);

  // Basic reset and legal-state checks
  a_reset_vals: assert property (!de_rstn |-> (l_cs==LWAIT && !go_line && !go_line_1 &&
                                               cpx==16'h0 && cpy==16'h0 &&
                                               delta_x==16'h0 && delta_y==16'h0 &&
                                               error_reg==16'h0 && einc_x==16'h0 && einc_y==16'h0 &&
                                               itr_count==16'h0));
  a_state_legal: assert property (l_cs inside {LWAIT,L1,L2,L3,L4,L5,L6,L7,L8,L9,LIDLE1});

  // Pipeline/control relationships
  a_go_line1:   assert property (go_line_1 == $past(load_actv_3d));
  a_go_line:    assert property (go_line == (line_actv_3d && $past(load_actv_3d)));
  a_active_0:   assert property ((l_cs==LWAIT && !go_line) |-> !l_active);
  a_active_1:   assert property (((l_cs!=LWAIT) || go_line) |-> l_active);

  // Derived wires must match regs
  a_eneg:  assert property (eneg == error_reg[15]);
  a_eeqz:  assert property (eeqz == (~|error_reg));
  a_eol:   assert property (eol  == (itr_count==16'h0));

  // Direction decode
  a_dirmaj_cap: assert property (l_ldmaj |=> dir_maj == $past(out_x[15]));
  a_dirmin_cap: assert property (l_ldmin |=> dir_min == {$past(out_y[15]), $past(out_x[15])});
  a_lrht_map:   assert property (l_rht == ((dir==o0)||(dir==o2)||(dir==o4)||(dir==o6)));
  a_ldwn_map:   assert property (l_dwn == ((dir==o0)||(dir==o1)||(dir==o4)||(dir==o5)));

  // Plines latch combinational outputs every cycle
  a_pline_x: assert property (1 |=> pline_x == $past(out_x));
  a_pline_y: assert property (1 |=> pline_y == $past(out_y));

  // Delta/einc captures
  a_dx_cap:   assert property (l_delta_x |=> delta_x == $past(out_x));
  a_dx_hold:  assert property (!l_delta_x |=> delta_x == $past(delta_x));
  a_dy_cap:   assert property (l_delta_y |=> delta_y == $past(out_y));
  a_dy_hold:  assert property (!l_delta_y |=> delta_y == $past(delta_y));
  a_einx_cap: assert property (l_einc_x  |=> einc_x  == $past(out_x));
  a_einy_cap: assert property (l_einc_y  |=> einc_y  == $past(out_y));

  // Error register update priority and exclusivity
  a_err_onehot: assert property (!(ld_error && (inc_err||rst_err)) && !(inc_err && rst_err));
  a_err_upd: assert property (
      1 |=> (
        $past(ld_error) ? (error_reg == $past(out_x)) :
        $past(inc_err)  ? (error_reg == $past(error_reg) + $past(einc_y)) :
        $past(rst_err)  ? (error_reg == $past(error_reg) - $past(einc_x)) :
                          (error_reg == $past(error_reg))
      )
  );

  // Iteration counter update
  a_itr_ld:   assert property ($past(ld_itr)  |-> itr_count == $past(delta_x));
  a_itr_dec:  assert property ($past(dec_itr) |-> itr_count == $past(itr_count) - 16'h1);
  a_itr_hold: assert property (!($past(ld_itr)||$past(dec_itr)) |-> itr_count == $past(itr_count));

  // Coordinate updates
  a_cpx_load: assert property ($past(go_line) |-> cpx == $past(cpx0));
  a_cpy_load: assert property ($past(go_line) |-> cpy == $past(cpy0));
  a_cpx_step_r: assert property ($past(l_chgx && l_rht && !go_line) |-> cpx == $past(cpx) + 16'h1);
  a_cpx_step_l: assert property ($past(l_chgx && !l_rht && !go_line) |-> cpx == $past(cpx) - 16'h1);
  a_cpx_hold:   assert property (!($past(go_line)||$past(l_chgx)) |-> cpx == $past(cpx));
  a_cpy_step_d: assert property ($past(l_chgy && l_dwn && !go_line) |-> cpy == $past(cpy) + 16'h1);
  a_cpy_step_u: assert property ($past(l_chgy && !l_dwn && !go_line) |-> cpy == $past(cpy) - 16'h1);
  a_cpy_hold:   assert property (!($past(go_line)||$past(l_chgy)) |-> cpy == $past(cpy));

  // Output protocol in L8
  a_pixreq_when: assert property ((l_cs==L8 && (!pipe_busy || (eol && nlst_2))) |-> l_pixreq);
  a_pixreq_not:  assert property ((l_cs==L8 && pipe_busy && !(eol && nlst_2)) |-> !l_pixreq);
  a_last_when:   assert property ((l_cs==L8 && eol && (!pipe_busy || nlst_2)) |-> l_last_pixel);
  a_last_imp:    assert property (l_last_pixel |-> (l_cs==L8 && eol));
  a_msk_last:    assert property ((l_cs==L8 && eol && nlst_2) |-> l_pc_msk_last);
  a_msk_last_imp:assert property (l_pc_msk_last |-> (l_cs==L8 && eol && nlst_2));
  a_incpat_when: assert property ((l_cs==L8 && !pipe_busy && (!eol || (eol && !nlst_2))) |-> l_incpat);
  a_incpat_imp:  assert property (l_incpat |-> (l_cs==L8 && !pipe_busy && (!eol || !nlst_2)));
  a_decitr_eq:   assert property ((l_cs==L8 && !pipe_busy && !eol) <-> dec_itr);

  // Quiet outputs in idle
  a_idle_quiet: assert property ((l_cs==LWAIT && !go_line) |-> (!l_pixreq && !l_last_pixel && !l_pc_msk_last && !l_incpat));

  // FSM next-state expectations
  a_st_wait: assert property ((l_cs==LWAIT) |-> ##1 (go_line ? (l_cs==L1) : (l_cs==LWAIT)));
  a_st_l1:   assert property ((l_cs==L1)   |-> ##1 l_cs==L2);
  a_st_l2:   assert property ((l_cs==L2)   |-> ##1 l_cs==L3);
  a_st_l3:   assert property ((l_cs==L3)   |-> ##1 l_cs==L4);
  a_st_l4:   assert property ((l_cs==L4)   |-> ##1 l_cs==L5);
  a_st_l5:   assert property ((l_cs==L5)   |-> ##1 l_cs==L6);
  a_st_l6:   assert property ((l_cs==L6)   |-> ##1 l_cs==L7);
  a_st_l7:   assert property ((l_cs==L7)   |-> ##1 ((pipe_busy) ? (l_cs==L8) : (l_cs==L9)));
  a_st_l9:   assert property ((l_cs==L9)   |-> ##1 l_cs==L8);
  a_st_l8:   assert property ((l_cs==L8)   |-> ##1 (l_cs inside {L8,LIDLE1}));
  a_st_idle1:assert property ((l_cs==LIDLE1)|-> ##1 l_cs==LWAIT);

  // Coverage

  // Cover all octants observed
  c_dir_o0: cover property (dir==o0);
  c_dir_o1: cover property (dir==o1);
  c_dir_o2: cover property (dir==o2);
  c_dir_o3: cover property (dir==o3);
  c_dir_o4: cover property (dir==o4);
  c_dir_o5: cover property (dir==o5);
  c_dir_o6: cover property (dir==o6);
  c_dir_o7: cover property (dir==o7);

  // Cover both L7 exits
  c_l7_to_l9: cover property ((l_cs==L7 && !pipe_busy) ##1 (l_cs==L9));
  c_l7_to_l8: cover property ((l_cs==L7 &&  pipe_busy) ##1 (l_cs==L8));

  // Cover both line-end cases
  c_end_nlst2_1: cover property (l_cs==L8 && eol && nlst_2 && l_pc_msk_last && l_last_pixel && l_pixreq ##1 l_cs==LIDLE1);
  c_end_nlst2_0: cover property (l_cs==L8 && !pipe_busy && eol && !nlst_2 && l_incpat && l_last_pixEl && l_pixreq ##1 l_cs==LIDLE1);
  // Note: l_last_pixEl typo? fix below
  // Fix coverage for end with !nlst_2
  c_end_nlst2_0_fix: cover property (l_cs==L8 && !pipe_busy && eol && !nlst_2 && l_incpat && l_last_pixel && l_pixreq ##1 l_cs==LIDLE1);

  // Cover step directions
  c_step_x_pos: cover property ($past(l_chgx && l_rht) && (cpx == $past(cpx)+1));
  c_step_x_neg: cover property ($past(l_chgx && !l_rht) && (cpx == $past(cpx)-1));
  c_step_y_pos: cover property ($past(l_chgy && l_dwn) && (cpy == $past(cpy)+1));
  c_step_y_neg: cover property ($past(l_chgy && !l_dwn) && (cpy == $past(cpy)-1));

  // Cover error register ops
  c_err_ld:  cover property ($past(ld_error)  && (error_reg == $past(out_x)));
  c_err_inc: cover property ($past(inc_err)   && (error_reg == $past(error_reg)+$past(einc_y)));
  c_err_rst: cover property ($past(rst_err)   && (error_reg == $past(error_reg)-$past(einc_x)));

  // Cover a full line from start to idle
  c_full_line: cover property (go_line ##[1:20] l_cs==L8 ##[1:$] eol ##1 l_cs==LIDLE1 ##1 l_cs==LWAIT);

endmodule