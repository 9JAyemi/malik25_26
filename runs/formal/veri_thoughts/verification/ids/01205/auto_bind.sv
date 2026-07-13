// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): connect_decoder_input_to_select2, assert, property, disable, iff, decoder_onehot_output, onehot, decoder_selected_bit_is_one, b1, decoder_matches_shift, b0000_0001, decoder_selected_bit_matches_index, counter_inst_reset_clears, b0000, counter_inst_increments, past, d1, local_counter_reset_clears, local_counter_increments, out_equals_and_of_selecteds, out_zero_when_decoder_bit_zero, b0, out_equals_counterbit_when_decoder_bit_one, out_is_zero_during_reset
bind top_module top_module_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .select1(select1),
    .select2(select2),
    .out(out),
    .counter(counter),
    .counter_output(counter_output),
    .decoder_input(decoder_input),
    .decoder_output(decoder_output),
    .posedge(posedge)
);
