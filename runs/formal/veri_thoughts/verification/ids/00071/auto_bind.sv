// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_post_reset_readdata_zero, assert, property, posedge, disable, iff, past, b0, h0000, check_addr0_read_matches_input_or_reset_zero, b1, b00, check_addr1_reads_zero, b01, check_addr2_reads_zero, b10, check_addr3_reads_zero, b11, check_addr0_zero_input_reads_zero, check_nonzero_readdata_from_addr0
bind pio_latency pio_latency_assertions auto_sva_inst (
    .address(address),
    .clk(clk),
    .in_port(in_port),
    .reset_n(reset_n),
    .readdata(readdata)
);
