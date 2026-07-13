module up_down_counter_sva (
    input logic       clk,
    input logic       up_down,
    input logic       reset,
    input logic [2:0] Q
);

    // Reset clears the counter on the next clock.
    check_reset_clears_q: assert property (
        @(posedge clk) reset |=> (Q == 3'b000)
    );

    // When not in reset and counting up, Q increments by one.
    check_count_up: assert property (
        @(posedge clk) disable iff (reset)
        up_down |=> (Q == ($past(Q) + 3'd1))
    );

    // When not in reset and counting down, Q decrements by one.
    check_count_down: assert property (
        @(posedge clk) disable iff (reset)
        !up_down |=> (Q == ($past(Q) - 3'd1))
    );

    // Counting up from 7 wraps back to 0.
    check_wrap_up_from_max: assert property (
        @(posedge clk) disable iff (reset)
        (Q == 3'b111 && up_down) |=> (Q == 3'b000)
    );

    // Counting down from 0 wraps back to 7.
    check_wrap_down_from_zero: assert property (
        @(posedge clk) disable iff (reset)
        (Q == 3'b000 && !up_down) |=> (Q == 3'b111)
    );

endmodule