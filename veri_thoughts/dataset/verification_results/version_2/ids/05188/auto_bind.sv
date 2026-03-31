// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_shift_register, assert, property, check_reset_clears_out_always_ff, b0, check_reset_clears_functional_output, check_shift_register_update, disable, iff, initstate, past, check_functional_module_logic, check_out_ff_captures_functional_output, check_out_ff_clears_after_high
bind shift_register top_module_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .d(d),
    .a(a),
    .b(b),
    .out_always_ff(out_always_ff),
    .shift_reg_out(shift_reg_out),
    .functional_module_out(functional_module_out),
    .posedge(posedge),
    .b000(b000)
);
