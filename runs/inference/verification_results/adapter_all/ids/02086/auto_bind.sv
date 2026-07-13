// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_outputs, assert, property, check_hold_when_disabled, disable, iff, past, check_increment_when_enabled, check_decrement_when_enabled, check_gray_map_00, check_gray_map_01, check_gray_map_11, check_gray_map_10, check_functional_module_concatenation
bind gray_counter gray_counter_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .up_down(up_down),
    .enable(enable),
    .counter_out(counter_out),
    .gray_out(gray_out),
    .posedge(posedge),
    .b00(b00),
    .b01(b01),
    .b11(b11),
    .b10(b10),
    .q(q)
);
