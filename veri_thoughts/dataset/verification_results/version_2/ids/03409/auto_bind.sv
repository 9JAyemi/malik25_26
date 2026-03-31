// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_invalid_read_zero, assert, property, posedge, disable, iff, b110, b111, b0, check_post_reset_output_zero, initstate, past, check_hold_no_write_stable_read, b1, check_hold_write_other_addr, check_write_addr0_readback, b000, check_write_addr1_readback, b001, check_write_addr2_readback, b010, check_write_addr3_readback, b011, check_write_addr4_readback, b100, check_write_addr5_readback, b101
bind sync_ram sync_ram_sva auto_sva_inst (
    .clk(clk),
    .datain(datain),
    .write_reset(write_reset),
    .waddr(waddr),
    .raddr(raddr),
    .we(we),
    .dataout(dataout)
);
