// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): shifted_data, check_reset_clears_regs, assert, property, posedge, b0000, check_count_follows_shifted_data, disable, iff, past, check_shift00_when_shift_right, b00, check_shift00_when_not_shift_right, check_shift01_when_shift_left, b01, check_shift01_when_not_shift_left, check_shift10_when_rotate_right, b10, check_shift10_when_not_rotate_right, check_shift11_when_rotate_left, b11, check_shift11_when_not_rotate_left
bind barrel_shift_up_down_counter barrel_shift_up_down_counter_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .select(select),
    .data_in(data_in),
    .shift(shift),
    .shift_right(shift_right),
    .shift_left(shift_left),
    .rotate_right(rotate_right),
    .rotate_left(rotate_left),
    .count(count)
);
