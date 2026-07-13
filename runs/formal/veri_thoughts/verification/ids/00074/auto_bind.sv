// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_counter, assert, property, b0000, b1111, check_countbar0_is_complement, or, disable, iff, check_countbar1_is_complement, check_countbar2_is_complement, check_countbar3_is_complement, check_count0_captures_inverted_feedback, b1, past, check_count1_captures_inverted_feedback, check_count2_captures_inverted_feedback, check_count3_captures_inverted_feedback, check_counter_decrements_each_clk, d1
bind jAsyncCntrDFlipFlop jAsynchronousCounter_sva auto_sva_inst (
    .clk(clk),
    .rst(rst),
    .count(count),
    .countbar(countbar),
    .posedge(posedge)
);
