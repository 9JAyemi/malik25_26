// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_aclr_clears_q, assert, property, posedge, b000, check_sclr_clears_q, disable, iff, check_sclr_priority_over_count, check_count_up, past, b001, check_count_down, check_hold_when_disabled
bind small_fifo_cntr small_fifo_cntr_sva auto_sva_inst (
    .aclr(aclr),
    .clock(clock),
    .cnt_en(cnt_en),
    .updown(updown),
    .q(q),
    .sclr(sclr)
);
