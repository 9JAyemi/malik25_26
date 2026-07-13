module up_down_counter_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic [2:0] count
);

    // Active-low reset forces count to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) (reset == 1'b0) |-> (count == 3'b000)
    );

    // When enabled, count increments by one on the next clock.
    check_count_increments: assert property (
        @(posedge clk) disable iff (reset == 1'b0)
        (enable == 1'b1) |=> (count == ($past(count) + 3'b001))
    );

    // When not enabled, count decrements by one on the next clock.
    check_count_decrements: assert property (
        @(posedge clk) disable iff (reset == 1'b0)
        (enable != 1'b1) |=> (count == ($past(count) - 3'b001))
    );

    // Incrementing from 7 wraps back to 0.
    check_increment_wraps_to_zero: assert property (
        @(posedge clk) disable iff (reset == 1'b0)
        (enable == 1'b1) && (count == 3'b111) |=> (count == 3'b000)
    );

    // Decrementing from 0 wraps back to 7.
    check_decrement_wraps_to_seven: assert property (
        @(posedge clk) disable iff (reset == 1'b0)
        (enable != 1'b1) && (count == 3'b000) |=> (count == 3'b111)
    );

    // Outside reset, count must change every clock.
    check_count_never_stalls: assert property (
        @(posedge clk) disable iff (reset == 1'b0)
        1'b1 |=> (count != $past(count))
    );

endmodule