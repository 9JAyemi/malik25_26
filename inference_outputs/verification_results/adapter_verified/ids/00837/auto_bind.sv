// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_out_port, assert, property, posedge, h00, check_reset_clears_readdata, h00000000, check_write_loads_out_port, disable, iff, h0, past, check_nonzero_address_ignored, check_chipselect_low_ignored, b0, check_write_n_high_ignored, b1, check_read_address_0_returns_out_port, check_read_nonzero_address_returns_zero
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
