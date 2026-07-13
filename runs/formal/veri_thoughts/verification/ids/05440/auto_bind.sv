// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_digits, assert, property, posedge, d0, check_clear_sets_zero, disable, iff, check_hold_when_idle, past, check_inc_without_carry, d9, d1, check_inc_with_carry, check_inc_wraps_99_to_00, check_dec_floor_to_ten, d2, check_dec_borrow_from_x1, check_dec_borrow_from_x0, d8, check_dec_subtracts_two
bind score_counter score_counter_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .d_inc(d_inc),
    .d_dec(d_dec),
    .d_clr(d_clr),
    .dig0(dig0),
    .dig1(dig1)
);
