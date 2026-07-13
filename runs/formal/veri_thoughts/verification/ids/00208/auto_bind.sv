// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_counter1_counts_up, assert, property, past, d1, check_counter1_counts_down, check_counter2_counts_up, check_counter2_counts_down, check_adder_sum, check_out_lower_matches_adder, check_out_upper_matches_shift, check_adder_counts_up_by_two, d2, check_adder_counts_down_by_two
bind up_down_counter shift_and_sum_sva auto_sva_inst (
    .clk(clk),
    .up_down(up_down),
    .A(A),
    .B(B),
    .out(out),
    .counter1_out(counter1_out),
    .counter2_out(counter2_out),
    .binary_adder_out(binary_adder_out),
    .posedge(posedge)
);
