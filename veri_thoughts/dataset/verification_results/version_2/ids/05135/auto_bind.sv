// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_clears_out_port, assert, property, posedge, b00, reset_clears_readdata, b0, read_upper_bits_zero, disable, iff, read_addr_zero_returns_out_port, read_nonzero_addr_returns_zero, write_addr_zero_captures_low_bits, past, unselected_cycle_holds_out_port, read_cycle_holds_out_port, write_nonzero_addr_holds_out_port
bind soc_system_pio_aliveTest_cpu_s0 soc_system_pio_aliveTest_cpu_s0_sva auto_sva_inst (
    .address(address),
    .chipselect(chipselect),
    .clk(clk),
    .reset_n(reset_n),
    .write_n(write_n),
    .writedata(writedata),
    .out_port(out_port),
    .readdata(readdata)
);
