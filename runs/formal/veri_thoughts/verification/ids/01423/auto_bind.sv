// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): higher_zero_when_lower_selected, assert, property, disable, iff, lower_zero_when_higher_selected, act_equals_lower_on_lower_select, act_equals_higher_on_higher_select, bigN_checks, lower_segment_bigN, higher_segment_bits_bigN, higher_segment_upper_zero_bigN, smallN_checks, lower_segment_lowbits_smallN, lower_segment_upper_zero_smallN, higher_segment_zero_smallN
bind intr_capturer intr_capturer_sva auto_sva_inst (
    .read(read),
    .rddata(rddata),
    .b0(b0),
    .posedge(posedge),
    .clk(clk),
    .rst_n(rst_n),
    .access_lower_32(access_lower_32),
    .readdata_higher_intr(readdata_higher_intr),
    .access_higher_32(access_higher_32),
    .readdata_lower_intr(readdata_lower_intr),
    .act_readdata(act_readdata),
    .if(if),
    .NUM_INTR(NUM_INTR),
    .begin(begin),
    .interrupt_reg(interrupt_reg),
    .end(end),
    .else(else)
);
