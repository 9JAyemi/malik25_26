// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_q_next, assert, property, posedge, b0000, check_hold_zero_while_reset, past, check_inc_on_up_only, disable, iff, b1, check_dec_on_down_only, check_hold_on_both_low, check_hold_on_both_high, check_step_bounded_no_reset, check_change_requires_one_hot_cmd, check_inc_implies_up_only, check_dec_implies_down_only
bind full_adder up_down_counter_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .Up(Up),
    .Down(Down),
    .Q(Q)
);
