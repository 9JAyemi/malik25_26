// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_clears_outputs, assert, property, posedge, h0, write_addr0_updates_out_port, disable, iff, b00, past, no_chipselect_holds_out_port, write_high_holds_out_port, write_nonzero_addr_ignored, read_addr0_returns_out_port, read_nonzero_addr_returns_zero, readdata_upper_bits_zero
bind memory_module memory_module_sva auto_sva_inst (
    .address(address),
    .chipselect(chipselect),
    .clk(clk),
    .reset_n(reset_n),
    .write_n(write_n),
    .writedata(writedata),
    .out_port(out_port),
    .readdata(readdata)
);
