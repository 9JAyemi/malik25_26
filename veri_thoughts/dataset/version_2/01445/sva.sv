module async_counter_sva (
    input logic clk,
    input logic reset,       // Asynchronous active-high reset
    input logic up_down,     // Count direction: 1=up, 0=down
    input logic [2:0] q
);
    // While reset is asserted, q must be 0 on each clock.
    reset_holds_zero: assert property (
        @(posedge clk) reset |-> (q == 3'b000)
    );

    // When counting up, q increments by 1 modulo 8.
    count_up_increments: assert property (
        @(posedge clk) disable iff (reset) (up_down && $past(1'b1)) |-> (q == ($past(q) + 3'd1))
    );

    // When counting down, q decrements by 1 modulo 8.
    count_down_decrements: assert property (
        @(posedge clk) disable iff (reset) (!up_down && $past(1'b1)) |-> (q == ($past(q) - 3'd1))
    );

    // Increment from 7 wraps to 0.
    wrap_up_from_7_to_0: assert property (
        @(posedge clk) disable iff (reset) (up_down && $past(1'b1) && ($past(q) == 3'd7)) |-> (q == 3'd0)
    );

    // Decrement from 0 wraps to 7.
    wrap_down_from_0_to_7: assert property (
        @(posedge clk) disable iff (reset) (!up_down && $past(1'b1) && ($past(q) == 3'd0)) |-> (q == 3'd7)
    );

    // On every non-reset cycle, q must change (never holds its value).
    non_reset_always_changes: assert property (
        @(posedge clk) disable iff (reset) $past(1'b1) |-> (q != $past(q))
    );

    // If up_down stays high for two cycles, q advances by +2 modulo 8.
    two_cycle_up_add2: assert property (
        @(posedge clk) disable iff (reset) (up_down && $past(up_down) && $past(1'b1,2)) |-> (q == ($past(q,2) + 3'd2))
    );

    // If up_down stays low for two cycles, q retreats by -2 modulo 8.
    two_cycle_down_sub2: assert property (
        @(posedge clk) disable iff (reset) (!up_down && !$past(up_down) && $past(1'b1,2)) |-> (q == ($past(q,2) - 3'd2))
    );

    // On reset deassert with up count, q becomes 1 (0 + 1).
    release_to_up_starts_at1: assert property (
        @(posedge clk) disable iff (reset) ($fell(reset) && up_down) |-> (q == 3'd1)
    );

    // On reset deassert with down count, q becomes 7 (0 - 1).
    release_to_down_starts_at7: assert property (
        @(posedge clk) disable iff (reset) ($fell(reset) && !up_down) |-> (q == 3'd7)
    );
endmodule