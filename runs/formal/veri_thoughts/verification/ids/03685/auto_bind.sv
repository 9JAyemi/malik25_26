// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): shift_reg, shift_reg_next, shift_reg_last, clk_shifted_last, int, n, check_shift_reg_last_tracks_shift_reg, assert, property, posedge, b1, past, check_clk_shifted_last_tracks_clk_shifted, check_shift_reg_next_lsb_loads_clock_high, check_shift_reg_next_upper_bits_shift_previous_reg, check_shift_reg_tracks_previous_next, check_zero_shift_drives_high_next_cycle, h00, check_nonzero_shift_uses_delayed_tap, check_shift_reg_eventually_all_ones, hFF, check_shift_reg_last_eventually_all_ones, check_clk_shifted_eventually_high
bind clk_phase_shifter clk_phase_shifter_sva auto_sva_inst (
    .clk(clk),
    .shift(shift),
    .clk_shifted(clk_shifted)
);
