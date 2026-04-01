// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_count_clk_clears_on_10_or_11, assert, property, posedge, b10, b11, d0, check_position_registers_capture_on_01_10_11, b01, stable, past, check_position_registers_update_on_00, b00, d1, d, check_position_registers_increment_on_m1, b1, check_position_registers_decrement_on_m1, b0, check_position_registers_increment_on_m2, check_position_registers_decrement_on_m2, check_pos_diff_x_clears_on_10_or_11, check_pos_diff_y_clears_on_10_or_11, check_pos_diff_x_update_on_00, check_pos_diff_y_update_on_00
bind posManager posManager_sva auto_sva_inst (
    .clk(clk),
    .pos11(pos11),
    .pos12(pos12),
    .pos21(pos21),
    .pos22(pos22),
    .pos_diff_x(pos_diff_x),
    .pos_diff_y(pos_diff_y),
    .count_clk(count_clk),
    .clear(clear),
    .m1(m1),
    .m2(m2)
);
