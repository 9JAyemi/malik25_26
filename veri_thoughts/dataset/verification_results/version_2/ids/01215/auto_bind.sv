// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_known_values, assert, property, dout_reflects_flags, disable, iff, write_cmd01_sets_busy, write_cmd10_clears_busy_and_done, write_cmd11_no_change, past, write_cmd00_no_change, write_group_non00_no_change, read_access_no_change, non_target_access_no_change, busy_implies_done_low
bind nova_io_pio_dummy nova_io_pio_dummy_sva auto_sva_inst (
    .pclk(pclk),
    .bs_rst(bs_rst),
    .bs_stb(bs_stb),
    .bs_we(bs_we),
    .bs_adr(bs_adr),
    .bs_din(bs_din),
    .bs_dout(bs_dout),
    .r_DONE(r_DONE),
    .r_BUSY(r_BUSY),
    .device_addr(device_addr),
    .b000000(b000000),
    .posedge(posedge),
    .b1(b1),
    .b0(b0),
    .h0000(h0000),
    .b00(b00),
    .b01(b01),
    .b10(b10),
    .b11(b11)
);
