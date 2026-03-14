module dff_async_reset_sva (
    input logic clk,
    input logic reset,
    input logic d,
    input logic q
);
    // Q matches previous D on cycles following a non-reset cycle.
    check_capture_from_d_prev_not_reset: assert property (
        @(posedge clk) disable iff (!reset)
            ($past(reset) == 1'b1) |-> (q == $past(d))
    );

    // Q is 0 on any cycle immediately following a cycle with reset low.
    check_q_zero_after_prev_reset_low: assert property (
        @(posedge clk) disable iff (!reset)
            ($past(reset) == 1'b0) |-> (q == 1'b0)
    );

    // Rising edge on D with reset high drives Q to 1 on the next clock.
    check_d_rise_sets_q_next: assert property (
        @(posedge clk) disable iff (!reset)
            (reset && $rose(d)) |=> (q == 1'b1)
    );

    // Falling edge on D with reset high drives Q to 0 on the next clock.
    check_d_fall_clears_q_next: assert property (
        @(posedge clk) disable iff (!reset)
            (reset && $fell(d)) |=> (q == 1'b0)
    );

    // When reset high and D equals current Q, Q holds its value next cycle.
    check_q_holds_when_d_equals_q: assert property (
        @(posedge clk) disable iff (!reset)
            (reset && (d == q)) |=> (q == $past(q))
    );

    // With no reset over two cycles and stable D, Q remains stable across cycles.
    check_q_stable_when_d_stable: assert property (
        @(posedge clk) disable iff (!reset)
            (($past(reset) == 1'b1) && (reset == 1'b1) && (d == $past(d))) |=> (q == $past(q))
    );
endmodule