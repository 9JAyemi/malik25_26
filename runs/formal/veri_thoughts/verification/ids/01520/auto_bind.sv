// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): int, H_FRONT, H_SYNC, V_FRONT, V_SYNC, check_counterX_increments, assert, property, past, check_counterX_wrap, d0, check_counterY_hold_when_X_not_max, check_counterY_increment_on_Xmax, check_counterY_wrap_on_both_max, check_counterY_changes_only_on_prev_Xmax, check_vga_h_sync_definition, check_vga_v_sync_definition, check_inDisplayArea_definition, check_vga_h_sync_low_outside_window, b0, check_vga_v_sync_low_outside_window
bind hvsync_generator hvsync_generator_sva auto_sva_inst (
    .clk(clk),
    .vga_h_sync(vga_h_sync),
    .vga_v_sync(vga_v_sync),
    .inDisplayArea(inDisplayArea),
    .CounterX(CounterX),
    .CounterY(CounterY),
    .WIDTH(width),
    .HEIGHT(height),
    .COUNT_DOTS(count_dots),
    .COUNT_LINES(count_lines),
    .posedge(posedge),
    .d1(d1)
);
