// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_clears_outputs, assert, property, posedge, d0, readdata_upper_zero_always, disable, iff, read_addr0_reflects_out_port, read_addr_nonzero_is_zero, out_port_update_rule, past, out_port_holds_without_write, write_other_addr_no_effect, write_prev_cycle_updates_out, hold_when_write_n_high_addr0, zero_after_reset_release_no_write, rose
bind wasca_hexdot wasca_hexdot_sva auto_sva_inst (
    .clk(clk),
    .reset_n(reset_n),
    .address(address),
    .chipselect(chipselect),
    .write_n(write_n),
    .writedata(writedata),
    .out_port(out_port),
    .readdata(readdata)
);
