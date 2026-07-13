module delay_1ms_sva (
    input logic        clk,
    input logic        reset,
    input logic        in,
    input logic        out,
    input logic [19:0] r
);

    // Reset clears the counter and output by the next sampled clock.
    check_reset_clears_state: assert property (
        @(posedge clk) reset |=> (r == 20'd0 && out == 1'b0)
    );

    // The first cycle after reset release still sees a cleared state.
    check_reset_release_starts_cleared: assert property (
        @(posedge clk) reset ##1 !reset |-> (r == 20'd0 && out == 1'b0)
    );

    // The output reflects whether the counter has reached the 1000-count threshold.
    check_output_matches_threshold: assert property (
        @(posedge clk) disable iff (reset) out == (r >= 20'd1000)
    );

    // A low input clears the counter and deasserts the output on the next clock.
    check_input_low_clears_state: assert property (
        @(posedge clk) disable iff (reset) !in |=> (r == 20'd0 && out == 1'b0)
    );

    // A high input increments the counter by one on the next clock.
    check_input_high_increments_counter: assert property (
        @(posedge clk) disable iff (reset) in |=> (r == ($past(r) + 20'd1))
    );

    // Reaching 999 with input high makes the output assert on the next cycle.
    check_threshold_crossing_sets_output: assert property (
        @(posedge clk) disable iff (reset) (in && (r == 20'd999)) |=> out
    );

endmodule