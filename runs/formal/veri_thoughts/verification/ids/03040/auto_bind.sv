// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_outputs, assert, property, posedge, b0, check_read_addr0_returns_out_port, disable, iff, b00, check_read_nonzero_addr_returns_zero, check_write_addr0_updates_out_port, past, check_no_target_write_holds_out_port, check_nonzero_address_write_is_ignored
bind pio_egmenable pio_egmenable_sva auto_sva_inst (
    .address(address),
    .chipselect(chipselect),
    .clk(clk),
    .reset_n(reset_n),
    .write_n(write_n),
    .writedata(writedata),
    .out_port(out_port),
    .readdata(readdata)
);
