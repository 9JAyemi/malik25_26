// SVA for mig_7series_v4_0_ddr_phy_ck_addr_cmd_delay
// Place inside the module or bind to its scope. Focused, high-value checks + coverage.

`ifdef ASSERT_ON
  // Default clocking/reset
  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Basic X-checks on outputs
  assert property (!$isunknown({po_stg2_f_incdec,po_en_stg2_f,po_stg2_c_incdec,po_en_stg2_c,po_ck_addr_cmd_delay_done}));

  // Stage2 control must mirror po_cnt_{dec,inc}
  assert property (po_en_stg2_f == po_cnt_dec);
  assert property (po_stg2_f_incdec == 1'b0);
  assert property (po_en_stg2_c == po_cnt_inc);
  assert property (po_stg2_c_incdec == po_cnt_inc);

  // po_cnt_inc/dec are mutually exclusive and 1-cycle pulses, only when started
  assert property (!(po_cnt_inc && po_cnt_dec));
  assert property (po_cnt_inc |=> !po_cnt_inc);
  assert property (po_cnt_dec |=> !po_cnt_dec);
  assert property (po_cnt_inc |-> cmd_delay_start);
  assert property (po_cnt_dec |-> cmd_delay_start);

  // wait_cnt_r behavior
  assert property ((po_cnt_dec || po_cnt_inc) |=> wait_cnt_r == 4'd8);
  assert property ((!po_cnt_dec && !po_cnt_inc && cmd_delay_start && (wait_cnt_r > 0)) |=> wait_cnt_r == $past(wait_cnt_r) - 1);
  assert property ((!po_cnt_dec && !po_cnt_inc && (!cmd_delay_start || (wait_cnt_r == 0))) |=> wait_cnt_r == $past(wait_cnt_r));

  // po_cnt_dec legality and effect on delaydec_cnt_r
  assert property (po_cnt_dec |-> (wait_cnt_r == 4'd1) && (delaydec_cnt_r > 6'd0));
  assert property (po_cnt_dec |=> delaydec_cnt_r == $past(delaydec_cnt_r) - 1);
  assert property ((delaydec_cnt_r == 6'd0) |-> !po_cnt_dec);

  // po_cnt_inc legality and effect on delay_cnt_r
  localparam bit NO_INC = (tCK >= 2500) || (SIM_CAL_OPTION == "FAST_CAL");
  assert property (po_cnt_inc |-> (wait_cnt_r == 4'd1) && (delaydec_cnt_r == 6'd0) && (delay_cnt_r > 6'd0) && !NO_INC);
  assert property (po_cnt_inc |=> delay_cnt_r == $past(delay_cnt_r) - 1);
  assert property ((delay_cnt_r == 6'd0) |-> !po_cnt_inc);

  // delay_cnt_r rules
  if (NO_INC) begin
    assert property (1'b1 |-> (delay_cnt_r == 6'd0));
  end else begin
    assert property (((delaydec_cnt_r > 6'd0) || ((delay_cnt_r == 6'd0) && (ctl_lane_cnt != N_CTL_LANES-1))) |=> delay_cnt_r == 6'd1);
  end

  // delaydec_cnt_r reload rules
  assert property ((!cmd_delay_start) |=> delaydec_cnt_r == TAP_DEC);
  assert property (((delaydec_cnt_r == 6'd0) && (delay_cnt_r == 6'd0) && (ctl_lane_cnt != N_CTL_LANES-1)) |=> delaydec_cnt_r == TAP_DEC);

  // ctl_lane_cnt range and increment legality
  assert property (ctl_lane_cnt <= N_CTL_LANES-1);
  assert property ((ctl_lane_cnt != $past(ctl_lane_cnt)) |-> (ctl_lane_cnt == $past(ctl_lane_cnt) + 1) &&
                                                ($past(ctl_lane_cnt) != N_CTL_LANES-1) &&
                                                ($past(delaydec_cnt_r) == 6'd0) &&
                                                ($past(delay_cnt_r) == 6'd0));
  // Hold last lane under the stated condition
  assert property ((~delay_dec_done && (ctl_lane_cnt == N_CTL_LANES-1) && (delaydec_cnt_r == 6'd1)) |=> ctl_lane_cnt == $past(ctl_lane_cnt));

  // delay_dec_done set/hold
  assert property ((((TAP_CNT == 0) && (TAP_DEC == 0)) ||
                   ((delaydec_cnt_r == 6'd0) && (delay_cnt_r == 6'd0) && (ctl_lane_cnt == N_CTL_LANES-1))) |=> delay_dec_done);
  assert property ((delay_dec_done && cmd_delay_start) |=> delay_dec_done);

  // Pipeline of done flags
  assert property (delay_done_r1 == $past(delay_dec_done));
  assert property (delay_done_r2 == $past(delay_done_r1));
  assert property (delay_done_r3 == $past(delay_done_r2));
  assert property (delay_done_r4 == $past(delay_done_r3));

  // Output done mapping
  if (TAP_DEC == 0) begin
    assert property (po_ck_addr_cmd_delay_done);
  end else begin
    assert property (po_ck_addr_cmd_delay_done == delay_done_r4);
  end

  // Coverage
  // One lane step: dec to zero, one inc, then lane increments
  cover property ((TAP_DEC != 0) && cmd_delay_start
                  ##1 (po_cnt_dec && (delaydec_cnt_r > 0)) [*1:$]
                  ##1 (delaydec_cnt_r == 0)
                  ##1 po_cnt_inc
                  ##1 (ctl_lane_cnt == $past(ctl_lane_cnt) + 1));

  // Full completion: last lane done -> delay_dec_done -> 4-cycle pipeline to po_ck_addr_cmd_delay_done
  cover property ((TAP_DEC != 0) && cmd_delay_start
                  ##1 (ctl_lane_cnt == N_CTL_LANES-1) and (delaydec_cnt_r == 0) and (delay_cnt_r == 0)
                  ##1 delay_dec_done
                  ##1 delay_done_r1 ##1 delay_done_r2 ##1 delay_done_r3 ##1 delay_done_r4
                  ##0 po_ck_addr_cmd_delay_done);

  // FAST_CAL immediate done
  cover property ((TAP_DEC == 0) && !rst ##1 po_ck_addr_cmd_delay_done);

  // No-inc mode (tCK large or FAST_CAL): ensure no inc activity over a window
  cover property (NO_INC && cmd_delay_start ##1 (!po_cnt_inc)[*16]);
`endif