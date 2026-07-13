// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_outputs, assert, property, h00000000, check_readdata_upper_bits_zero, disable, iff, check_address0_reads_input, b00, past, check_unmapped_addresses_read_zero, b10, check_irq_requires_input_high, check_write_zero_clears_irq, check_write_one_sets_irq_behavior, b1, check_address2_read_matches_prev_irq_when_input_high, check_write_zero_readback_at_address2, check_write_one_readback_at_address2, h00000001
bind nios_dut_pio_0 nios_dut_pio_0_sva auto_sva_inst (
    .address(address),
    .chipselect(chipselect),
    .clk(clk),
    .in_port(in_port),
    .reset_n(reset_n),
    .write_n(write_n),
    .writedata(writedata),
    .irq(irq),
    .readdata(readdata),
    .posedge(posedge),
    .b0(b0)
);
