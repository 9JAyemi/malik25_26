// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_by_next_event, assert, property, negedge, or, posedge, rose, h00, check_reset_holds_zero_while_active, disable, iff, initstate, past, check_load_captures_data_in, check_shift_right_rotate, b00, check_shift_left_rotate, b01, check_invalid_direction_holds_value, b10, b11
bind shift_register shift_register_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .data_in(data_in),
    .shift_direction(shift_direction),
    .load(load),
    .data_out(data_out)
);
