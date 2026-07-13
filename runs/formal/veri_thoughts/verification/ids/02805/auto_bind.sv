// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_outputs_known_values, assert, property, h00, check_rdata_const_zero, disable, iff, check_full_implies_not_empty, check_empty_implies_not_full, check_full_implies_used_zero, check_empty_implies_used_zero, check_full_empty_mutex, check_status_stable_if_no_prev_read, past, check_empty_read_wraps_to_full, check_full_read_keeps_used_zero
bind NIOS_SYSTEMV3_JTAG_UART_sim_scfifo_r NIOS_SYSTEMV3_JTAG_UART_sim_scfifo_r_sva auto_sva_inst (
    .clk(clk),
    .fifo_rd(fifo_rd),
    .rst_n(rst_n),
    .fifo_EF(fifo_EF),
    .fifo_rdata(fifo_rdata),
    .rfifo_full(rfifo_full),
    .rfifo_used(rfifo_used),
    .posedge(posedge),
    .b1(b1),
    .b0(b0)
);
