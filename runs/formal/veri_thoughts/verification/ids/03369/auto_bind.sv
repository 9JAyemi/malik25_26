// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_outputs, assert, property, posedge, b0, h00000000, check_write_to_addr0_updates_out_port, disable, iff, b00, past, check_no_valid_write_holds_out_port, check_read_from_addr0_updates_readdata_lsb, check_no_valid_read_holds_readdata, check_write_then_next_read_returns_written_data
bind memory_block memory_block_sva auto_sva_inst (
    .address(address),
    .chipselect(chipselect),
    .clk(clk),
    .reset_n(reset_n),
    .write_n(write_n),
    .writedata(writedata),
    .out_port(out_port),
    .readdata(readdata)
);
