// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_post_reset_zero, assert, property, posedge, disable, iff, rose, h00000000, check_no_write_holds_state, past, check_write_add, b00, check_write_sub, b01, check_write_and, b10, check_write_or, b11, check_read_low_addresses_return_state, check_read_high_addresses_return_zero
bind nios_system_alu_a nios_system_alu_a_sva auto_sva_inst (
    .address(address),
    .chipselect(chipselect),
    .clk(clk),
    .reset_n(reset_n),
    .write_n(write_n),
    .writedata(writedata),
    .out_port(out_port),
    .readdata(readdata)
);
