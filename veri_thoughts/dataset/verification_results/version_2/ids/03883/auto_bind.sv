// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): counter, check_counter_zero_while_reset_low, assert, property, posedge, d0, check_counter_increments_on_enable, disable, iff, past, d1, check_counter_holds_when_disabled, check_counter_wraps_after_max, hF, h0, check_q_selects_data_in, check_q_selects_ff_on_control, hFF, check_q_selects_counter_on_control_low, check_q_counter_path_zero_during_reset, h00
bind counter_mux counter_mux_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .enable(enable),
    .control(control),
    .select(select),
    .data_in(data_in),
    .q(q)
);
