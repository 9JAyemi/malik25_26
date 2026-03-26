module up_counter_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] count
);

    // Count matches the previous cycle's reset-or-increment update.
    check_state_transition: assert property (
        @(posedge clk) disable iff ($initstate)
        count == ($past(reset) ? 4'b0000 : ($past(count) + 4'd1))
    );

    // A reset cycle clears the counter to zero on the next sampled cycle.
    check_reset_clears_count: assert property (
        @(posedge clk) disable iff ($initstate)
        reset |=> (count == 4'b0000)
    );

    // A non-reset cycle increments the counter by one on the next sampled cycle.
    check_increment_on_non_reset: assert property (
        @(posedge clk) disable iff ($initstate)
        !reset |=> (count == ($past(count) + 4'd1))
    );

    // After reset is released, the first observed count value is zero.
    check_release_from_reset_zero: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        $past(reset) |-> (count == 4'b0000)
    );

    // The 4-bit counter rolls over from 15 back to 0.
    check_rollover_from_max: assert property (
        @(posedge clk) disable iff ($initstate)
        (!reset && (count == 4'hF)) |=> (count == 4'h0)
    );

endmodule