// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_decoder_enable_forces_zero, assert, property, disable, iff, check_decoder_step_00_to_01, check_decoder_step_01_to_10, check_decoder_step_10_to_11, check_decoder_step_11_to_00, check_counter_reset_clears, check_counter_increments_when_enabled, past, d1, check_counter_holds_when_disabled, check_func_reset_clears, check_func_updates_when_selected, check_func_holds_when_not_selected, check_top_reset_clears_out, check_top_selects_func_path, check_top_selects_counter_path
bind top_module top_module_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .enable(enable),
    .select(select),
    .out(out),
    .decoder_out(decoder_out),
    .counter_out(counter_out),
    .func_out(func_out),
    .posedge(posedge),
    .b00(b00),
    .b01(b01),
    .b10(b10),
    .b11(b11),
    .b0000(b0000)
);
