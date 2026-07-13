// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_clears_out_port, assert, property, posedge, b0, reset_clears_readdata, write_addr0_updates_out_port, disable, iff, b00, past, no_write_addr0_holds_out_port, stable, read_addr0_returns_out_port, read_other_addresses_zero
bind spw_babasu_DATA_I spw_babasu_DATA_I_sva auto_sva_inst (
    .address(address),
    .chipselect(chipselect),
    .clk(clk),
    .reset_n(reset_n),
    .write_n(write_n),
    .writedata(writedata),
    .out_port(out_port),
    .readdata(readdata)
);
