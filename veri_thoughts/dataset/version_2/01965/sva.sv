module synchronous_counter_sva (
    input logic clk,
    input logic rst,
    input logic [3:0] count
);

    ///// Reset behavior /////
    // If rst is HIGH at a clock edge, count is 0 on the next cycle.
    reset_clears_next: assert property (
        @(posedge clk) rst |-> (count == 4'h0)
    );

    // While rst remains HIGH across cycles, count stays 0.
    hold_zero_during_reset: assert property (
        @(posedge clk) $past(rst) && rst |-> (count == 4'h0)
    );

    ///// Counting behavior (out of reset) /////
    // From 15 with rst LOW at both cycles, wrap to 0.
    wrap_from_15_noreset: assert property (
        @(posedge clk) disable iff (rst)
            (!$past(rst) && !rst && ($past(count) == 4'hF)) |-> (count == 4'h0)
    );

    // From non-15 with rst LOW at both cycles, next count increments or is 0 (async reset may have occurred between edges).
    step_or_zero_noreset: assert property (
        @(posedge clk) disable iff (rst)
            (!$past(rst) && !rst && ($past(count) != 4'hF)) |-> ((count == ($past(count) + 4'h1)) || (count == 4'h0))
    );

    // If not wrapping and next value is non-zero, it must be an exact +1 increment.
    strict_step_when_nonzero: assert property (
        @(posedge clk) disable iff (rst)
            (!$past(rst) && !rst && ($past(count) != 4'hF) && (count != 4'h0)) |-> (count == ($past(count) + 4'h1))
    );

    // If current is non-zero out of reset, it must have increased vs. previous sample (no hold/decrement).
    monotonic_increase_noreset: assert property (
        @(posedge clk) disable iff (rst)
            (!$past(rst) && !rst && (count != 4'h0)) |-> (count > $past(count))
    );

    // If current is non-zero out of reset, previous sample was not 15 (no non-zero after wrap).
    no_nonzero_after_prev_15: assert property (
        @(posedge clk) disable iff (rst)
            (!$past(rst) && !rst && (count != 4'h0)) |-> ($past(count) != 4'hF)
    );

endmodule