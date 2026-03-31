// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_sets_out_final, assert, property, posedge, disable, iff, initstate, h340, check_reset_sets_q, h00, h34, check_counter_increments_on_enable, past, d1, check_register_holds_on_enable, check_register_loads_d_on_disable, check_counter_holds_on_disable, check_q_selects_counter_when_enabled, b0000, check_q_selects_register_when_disabled
bind register_counter register_counter_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .enable(enable),
    .d(d),
    .q(q),
    .out_final(out_final)
);
