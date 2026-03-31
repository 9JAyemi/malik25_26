// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_top_out_follows_sum_out, assert, property, disable, iff, check_sum_out_matches_inputs, check_reset_clears_visible_outputs, past, check_shift_output_loads_data, check_shift_output_holds_when_sel_low, check_counter_low_path_holds, check_counter_high_path_behavior, b0001, check_shift_counter_high_path_behavior, check_top_output_holds_when_sel_low, check_top_output_high_path_behavior, b0010
bind shift_register_counter top_module_sva auto_sva_inst (
    .clk(clk),
    .rst(rst),
    .en(en),
    .load(load),
    .data_in(data_in),
    .sel(sel),
    .out(out),
    .shift_reg_out(shift_reg_out),
    .counter_out(counter_out),
    .sum_out(sum_out),
    .posedge(posedge),
    .b0000(b0000)
);
