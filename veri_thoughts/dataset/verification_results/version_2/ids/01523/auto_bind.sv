// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): counter, reset_clears_outputs_and_counter, assert, property, posedge, b0, d0, check_counter_bounded, disable, iff, h00FFFFF, inc_when_not_at_limit, past, d1, rty_low_when_not_at_limit, interrupt_unchanged_when_not_at_limit, clear_when_limit_and_bus_read, b1111_1111_1111_1111_1111_1111_111, b001, b1, set_interrupt_when_limit_without_clear, hold_counter_when_limit_without_clear, hold_rty_when_limit_without_clear, rty_rose_only_from_clear, rose, interrupt_rose_only_from_limit_no_clear, rty_is_single_cycle_pulse
bind timer timer_sva auto_sva_inst (
    .CLK_I(CLK_I),
    .RST_I(RST_I),
    .ADR_I(ADR_I),
    .CYC_I(CYC_I),
    .STB_I(STB_I),
    .WE_I(WE_I),
    .RTY_O(RTY_O),
    .interrupt_o(interrupt_o)
);
