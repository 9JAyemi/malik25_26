// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_clears_counter, assert, property, b0000, reset_clears_converter, reset_clears_q, b00000000, counter_increments, disable, iff, b1, past, d1, counter_wraps_from_15, hF, h0, converter_twos_comp_when_negative, converter_pass_through_when_positive, q_selects_counter, q_selects_converter, q_upper_nibble_zero
bind top_module top_module_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .signed_mag(signed_mag),
    .select(select),
    .q(q),
    .counter_out(counter_out),
    .converter_out(converter_out),
    .posedge(posedge)
);
