// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_output_update_rule, assert, property, posedge, past, b1, check_hold_when_wren_low, check_load_when_wren_high, check_change_requires_prev_write, check_two_cycle_hold_no_write, check_addr_change_no_effect_without_write, changed, check_byteenable_change_no_effect_without_write
bind top_module top_module_sva auto_sva_inst (
    .clk(clk),
    .address(address),
    .byteenable(byteenable),
    .wren(wren),
    .data_in(data_in),
    .data_out(data_out)
);
