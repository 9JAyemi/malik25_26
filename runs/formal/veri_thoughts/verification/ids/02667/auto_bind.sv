// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_clears_result_and_valid, assert, property, posedge, b0, valid_next_cycle_when_not_reset, disable, iff, b1, valid_stays_high_out_of_reset, past, add_result_correct, b00, sub_result_correct, b01, mul_result_correct, b10, div_result_correct_when_b_nonzero, b11, d0, valid_after_add, valid_after_sub, valid_after_mul
bind calculator calculator_sva auto_sva_inst (
    .clk(clk),
    .op(op),
    .a(a),
    .b(b),
    .reset(reset),
    .result(result),
    .valid(valid)
);
