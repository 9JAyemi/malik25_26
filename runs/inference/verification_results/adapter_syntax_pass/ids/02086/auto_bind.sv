// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_counter_clears_after_reset, assert, property, disable, iff, past, check_gray_clears_after_reset, check_q_clears_after_reset, h00, check_counter_holds_when_disabled, check_counter_increments_when_up, check_counter_decrements_when_down, check_gray_decode_00, check_gray_decode_01, check_gray_decode_11, check_gray_decode_10, check_q_matches_concatenation
bind gray_counter top_module_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .up_down(up_down),
    .enable(enable),
    .q(q),
    .counter_out(counter_out),
    .gray_out(gray_out),
    .posedge(posedge),
    .b00(b00),
    .b01(b01),
    .b11(b11),
    .b10(b10)
);
