// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): counter, check_counter_zero_after_reset, assert, property, posedge, disable, iff, initstate, past, d0, check_io_do_zero_after_reset, check_counter_clears_on_valid_write, h11, h12, h13, h14, check_counter_increments_without_valid_write, d1, check_io_do_addr_11, check_io_do_addr_12, check_io_do_addr_13, check_io_do_addr_14, check_io_do_zero_on_unmapped_address
bind softusb_timer softusb_timer_sva auto_sva_inst (
    .usb_clk(usb_clk),
    .usb_rst(usb_rst),
    .io_we(io_we),
    .io_a(io_a),
    .io_do(io_do)
);
