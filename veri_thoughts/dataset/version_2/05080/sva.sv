module binary_counter_assertions (
    input logic clk,
    input logic reset,
    input logic [3:0] count
);

    // Reset forces the counter output to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |-> (count == 4'd0)
    );

    // Counts below fifteen increment by one on the next cycle.
    check_count_increments: assert property (
        @(posedge clk) disable iff (reset)
        (count != 4'd15) |=> (count == ($past(count) + 4'd1))
    );

    // Fifteen wraps back to zero on the next cycle.
    check_count_wraps_to_zero: assert property (
        @(posedge clk) disable iff (reset)
        (count == 4'd15) |=> (count == 4'd0)
    );

    // Every non-reset cycle follows the implemented next-state function.
    check_next_state_function: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (count == (($past(count) == 4'd15) ? 4'd0 : ($past(count) + 4'd1)))
    );

endmodule