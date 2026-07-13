module up_down_counter_sva (
    input logic clk,
    input logic up_down,
    input logic reset,
    input logic [2:0] count
);

    // Active-high reset must drive count to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |-> (count == 3'b000)
    );

    // When up_down is high, count increments on the next clock.
    check_increment_when_up_down_high: assert property (
        @(posedge clk) disable iff (reset)
        up_down |=> (count == ($past(count) + 3'b001))
    );

    // When up_down is low, count decrements on the next clock.
    check_decrement_when_up_down_low: assert property (
        @(posedge clk) disable iff (reset)
        !up_down |=> (count == ($past(count) - 3'b001))
    );

    // Incrementing from the maximum value wraps back to zero.
    check_wrap_increment_from_max: assert property (
        @(posedge clk) disable iff (reset)
        (up_down && (count == 3'b111)) |=> (count == 3'b000)
    );

    // Decrementing from zero wraps back to the maximum value.
    check_wrap_decrement_from_zero: assert property (
        @(posedge clk) disable iff (reset)
        (!up_down && (count == 3'b000)) |=> (count == 3'b111)
    );

endmodule