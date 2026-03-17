// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_in_reset_forces_zero, assert, property, posedge, h00, check_post_reset_zero, past, check_deassert_no_write_keeps_zero, disable, iff, check_deassert_write_updates_next, check_write_updates_from_prev_cycle, check_hold_when_no_write
bind data_register data_register_sva auto_sva_inst (
    .reset(reset),
    .wenb(wenb),
    .in_data(in_data),
    .clk(clk),
    .out_data(out_data)
);
