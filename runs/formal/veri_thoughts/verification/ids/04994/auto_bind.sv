// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): ADD, b00, SUB, b01, MUL, b10, DIV, b11, check_sync_reset_clears_outputs, assert, property, posedge, h00, b0, check_valid_set_after_active_cycle, disable, iff, b1, check_add_updates_result, past, hFF, check_sub_updates_result, check_mul_updates_result, check_div_updates_result
bind calculator calculator_sva auto_sva_inst (
    .clk(clk),
    .rst(rst),
    .op(op),
    .num1(num1),
    .num2(num2),
    .result(result),
    .valid(valid)
);
