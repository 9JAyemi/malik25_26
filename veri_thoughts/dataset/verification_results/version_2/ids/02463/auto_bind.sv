// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): counter, out_ff, check_counter_increments, assert, property, posedge, disable, iff, initstate, past, b01, check_out_counter_is_prev_counter, check_counter_equals_out_counter_plus1, check_out_counter_increments, check_out_ff_captures_prev_out_comb_ff, check_out_comb_is_xor, check_out_ff_next_equals_prev_a_xor_out_ff, check_out_ff_toggles_when_prev_a_1, check_out_ff_holds_when_prev_a_0, check_out_comb_relates_to_prev_out_comb
bind xor_counter xor_counter_sva auto_sva_inst (
    .clk(clk),
    .a(a),
    .out_comb_ff(out_comb_ff),
    .out_counter(out_counter)
);
