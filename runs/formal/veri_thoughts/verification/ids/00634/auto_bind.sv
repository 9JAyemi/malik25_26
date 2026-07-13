// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_clears_parallel_out, assert, property, shift_loads_next_value, disable, iff, initstate, past, hold_without_shift, shift_msb_inserts_serial_in, shift_lower_bits_move_right, retain_zero_after_reset_no_shift, final_output_matches_logic, final_output_zero_when_parallel_zero, b0, final_output_one_requires_nonzero_parallel, b1
bind four_bit_comparator top_module_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .A(A),
    .B(B),
    .serial_in(serial_in),
    .shift(shift),
    .parallel_out(parallel_out),
    .final_output(final_output),
    .posedge(posedge),
    .b0000(b0000)
);
