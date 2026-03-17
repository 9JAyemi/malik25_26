// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): byte_count, sum_temp, sum_prev, sum_final, state, reset_values, assert, property, posedge, b00, d0, state00_next_is_01, disable, iff, b01, state00_updates, past, d1, state01_updates, state01_next_when_255, d255, b10, state01_next_when_not_255, state10_compute_final, state10_output_prev_final, state10_next_is_11, b11, state11_next_when_match, state11_hold_when_mismatch, byte_count_stable_outside_state00, sum_prev_stable_outside_state01, sum_temp_stable_in_10_11, inside, sum_final_stable_outside_state10, sum_stable_outside_state10
bind fletcher_checksum fletcher_checksum_sva auto_sva_inst (
    .clk(clk),
    .rst(rst),
    .data(data),
    .sum(sum)
);
