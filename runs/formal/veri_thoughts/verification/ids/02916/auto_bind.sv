// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_q_zero, assert, property, h00, reset_final_output_zero, load_captures_data, disable, iff, past, rotate_left_when_dir00, rotate_right_when_dir01, hold_when_dir_others, inside, b10, b11, min_is_bounded_by_inputs, min_is_one_of_inputs, min_selects_a_when_least, min_selects_b_when_least, final_output_is_and
bind shift_register top_module_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .data_in(data_in),
    .shift_direction(shift_direction),
    .load(load),
    .a(a),
    .b(b),
    .c(c),
    .d(d),
    .q(q),
    .min(min),
    .final_output(final_output),
    .posedge(posedge),
    .b00(b00),
    .b01(b01)
);
