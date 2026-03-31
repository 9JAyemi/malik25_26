// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_r_dat_zero, assert, property, check_fifo_ff_zero, check_empty_implies_zero_used, d0, check_used_holds_without_write, past, check_used_increments_on_write, d1, check_nonempty_sticky, check_empty_holds_without_write, check_write_from_empty_clears_empty, check_write_from_empty_sets_used_one
bind soc_system_jtag_uart_sim_scfifo_w soc_system_jtag_uart_sim_scfifo_w_sva auto_sva_inst (
    .clk(clk),
    .fifo_wdata(fifo_wdata),
    .fifo_wr(fifo_wr),
    .fifo_FF(fifo_FF),
    .r_dat(r_dat),
    .wfifo_empty(wfifo_empty),
    .wfifo_used(wfifo_used),
    .posedge(posedge),
    .h00(h00),
    .b0(b0)
);
