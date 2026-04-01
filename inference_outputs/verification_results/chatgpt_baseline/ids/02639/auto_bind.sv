// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_clears_dout_next, assert, property, posedge, d0, reset_holds_zero_while_asserted, past, hold_when_ce_low, disable, iff, accumulates_on_ce, change_requires_ce_prev, zero_operand_no_change, accumulate_from_zero, two_cycle_accumulate, unit_din0_increments_by_din1, d1, unit_din1_increments_by_din0
bind my_mac my_mac_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .ce(ce),
    .din0(din0),
    .din1(din1),
    .dout(dout)
);
