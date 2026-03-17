// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): prev_CLK_B, CLK_B, symbol, symbol_cnt, busy, data, data_cnt, track_prev_clk_b, assert, property, posedge, disable, iff, past, reset_clears_regs_next, d0, h00, rd_clears_rxne_next, rxne_fall_only_on_rd, fell, start_sets_busy_and_counters, b1, d9, d2, symbol_cnt_counts_down, d1, load_symbol_cnt3_and_dec_data_cnt, d3, end_of_frame_sets_rxne_and_clears_busy, symbol_shifts_on_clk_b_rise, data_shifts_right_on_sample, D_loads_from_shifted_data, busy_rise_requires_start, rose, busy_fall_requires_eof, data_stable_while_symbol_window
bind UART_Rx UART_Rx_sva auto_sva_inst (
    .CLK(CLK),
    .D(D),
    .RD(RD),
    .RST(RST),
    .RX(RX),
    .RXNE(RXNE),
    .b0(b0)
);
