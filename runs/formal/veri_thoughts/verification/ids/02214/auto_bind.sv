// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): state, databuf, bits_detected, act_cnt, leadvrf_cnt, datarcv_cnt, rpt_cnt, STATE_IDLE, b00, STATE_LEADVERIFY, b01, STATE_DATARCV, b10, int, LEADCODE_LO_THOLD, LEADCODE_HI_THOLD, LEADCODE_HI_RPT_THOLD, RPT_RELEASE_THOLD, BIT_ONE_THOLD, BIT_DETECT_THOLD, IDLE_THOLD, check_reset_values, assert, property, posedge, d0, h0000_0000, b0, check_act_cnt_incr, disable, iff, past, check_act_cnt_clear, check_leadvrf_incr, b1, check_leadvrf_clear, check_datarcv_incr, check_datarcv_clear, check_bits_clear_outside_datarcv, check_bits_incr_on_detect, check_bits_hold_no_detect, check_databuf_clear_outside_datarcv, check_databuf_hold_no_one_thold, check_databuf_set_on_one_thold, d32, check_ack_equals_decode, check_code_updates_on_ack, check_release_clears_code_ack, check_code_holds_no_event, check_rpt_cnt_reset_on_lead_rpt, check_rpt_cnt_incr_otherwise, check_idle_to_leadverify, check_leadverify_to_datarcv, check_datarcv_to_idle, d33
bind ir_rcv ir_rcv_sva auto_sva_inst (
    .clk50(clk50),
    .reset_n(reset_n),
    .ir_rx(ir_rx),
    .ir_code(ir_code),
    .ir_code_ack(ir_code_ack)
);
