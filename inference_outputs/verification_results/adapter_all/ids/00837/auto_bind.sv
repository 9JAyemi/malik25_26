// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_out_port, assert, property, posedge, h00, check_reset_clears_readdata, h00000000, check_read_address_zero_returns_out_port, disable, iff, b00, b0, check_read_nonzero_address_returns_zero, check_write_address_zero_updates_out_port, past, check_out_port_holds_without_selected_write
bind wasca_hexdot wasca_hexdot_sva auto_sva_inst (
    .address(address),
    .chipselect(chipselect),
    .clk(clk),
    .reset_n(reset_n),
    .write_n(write_n),
    .writedata(writedata),
    .out_port(out_port),
    .readdata(readdata)
);
