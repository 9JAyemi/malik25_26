// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_sets_zero_next, assert, property, posedge, h00, reset_overrides_write, b0, write_captures_in_data, disable, iff, past, hold_on_wenb_high, b1, reset_while_asserted_holds_zero, hold_zero_after_reset_if_no_write, no_update_when_wenb_high_despite_data_change, changed, stable_across_back_to_back_no_write, write_with_different_data_changes_reg
bind r_FAULT_STATUS r_FAULT_STATUS_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .wenb(wenb),
    .in_data(in_data),
    .reg_0x1F(reg_0x1F)
);
