// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_sets_out_port_all_ones, assert, property, posedge, b1111111111, write_to_data_register_updates_out_port, disable, iff, b00, past, no_data_register_write_holds_out_port, read_addr0_returns_out_port, b0, read_other_addresses_return_zero, read_upper_bits_are_zero
bind soc_system_led_pio soc_system_led_pio_sva auto_sva_inst (
    .address(address),
    .chipselect(chipselect),
    .clk(clk),
    .reset_n(reset_n),
    .write_n(write_n),
    .writedata(writedata),
    .out_port(out_port),
    .readdata(readdata)
);
