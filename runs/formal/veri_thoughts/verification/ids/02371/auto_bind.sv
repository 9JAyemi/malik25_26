// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_clears_output_next, assert, property, posedge, h00, output_zero_on_reset_fall, fell, output_zero_while_reset_held, past, hold_when_prev_disable, disable, iff, hold_next_when_disable_now, change_requires_prev_enable, stable_across_two_disable_cycles, stable
bind shift_register shift_register_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .enable(enable),
    .shift(shift),
    .parallel_in(parallel_in),
    .parallel_out(parallel_out)
);
