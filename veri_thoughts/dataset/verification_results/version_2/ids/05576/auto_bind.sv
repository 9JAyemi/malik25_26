// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_load_updates_counter, assert, property, past, check_hold_counter_when_disabled, check_increment_counter, d1, check_decrement_counter, check_gray_encoding, check_final_output_xor, check_final_output_shift_relation, b0, check_load_updates_gray, check_load_updates_final_output, check_outputs_hold_when_disabled, stable
bind top_module top_module_sva auto_sva_inst (
    .clk(clk),
    .up_down(up_down),
    .load(load),
    .en(en),
    .data_in(data_in),
    .counter_out(counter_out),
    .gray_out(gray_out),
    .final_output(final_output),
    .posedge(posedge)
);
