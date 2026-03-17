// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_out_port_zero, assert, property, posedge, b0, reset_readdata_zero, readdata_upper_zero_always, disable, iff, readdata_low_matches_out_port_on_addr0, b00, readdata_low_zero_on_addr_non0, write_updates_out_port, past, write_other_addr_does_not_change_out_port, out_port_holds_without_write_hit0, out_port_change_requires_prev_write_hit0, read_after_write_returns_written_value, b1
bind nios_system_sram_addr nios_system_sram_addr_sva auto_sva_inst (
    .address(address),
    .chipselect(chipselect),
    .clk(clk),
    .reset_n(reset_n),
    .write_n(write_n),
    .writedata(writedata),
    .out_port(out_port),
    .readdata(readdata)
);
