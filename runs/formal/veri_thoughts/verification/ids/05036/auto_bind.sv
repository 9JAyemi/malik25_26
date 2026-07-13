// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_out_port, assert, property, posedge, b0000, check_reset_clears_readdata, b0, check_readdata_upper_bits_zero, disable, iff, check_readback_at_address_zero, b00, check_readback_at_other_addresses, check_write_updates_out_port, past, check_out_port_holds_without_valid_write
bind led_controller led_controller_sva auto_sva_inst (
    .address(address),
    .chipselect(chipselect),
    .clk(clk),
    .reset_n(reset_n),
    .write_n(write_n),
    .writedata(writedata),
    .out_port(out_port),
    .readdata(readdata)
);
