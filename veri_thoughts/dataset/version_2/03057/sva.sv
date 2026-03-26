module up_down_counter_sva (
    input logic       clk,
    input logic       reset,
    input logic       up_down,
    input logic [2:0] count
);

    // Clock: clk; reset: active-low asynchronous reset; logic: sequential 3-bit up/down counter.

    // When reset is low, the counter must be at zero.
    check_reset_clears_count: assert property (
        @(posedge clk) !reset |-> (count == 3'b000)
    );

    // When counting up, the next count increments by one modulo 8.
    check_count_up_step: assert property (
        @(posedge clk) disable iff (!reset)
        up_down |=> (count == ($past(count) + 3'd1))
    );

    // When counting down, the next count decrements by one modulo 8.
    check_count_down_step: assert property (
        @(posedge clk) disable iff (!reset)
        !up_down |=> (count == ($past(count) - 3'd1))
    );

    // Incrementing from the maximum value wraps to zero.
    check_up_wraps_from_max: assert property (
        @(posedge clk) disable iff (!reset)
        (up_down && (count == 3'b111)) |=> (count == 3'b000)
    );

    // Decrementing from zero wraps to the maximum value.
    check_down_wraps_from_zero: assert property (
        @(posedge clk) disable iff (!reset)
        (!up_down && (count == 3'b000)) |=> (count == 3'b111)
    );

    // Outside reset, the counter changes on every clock edge.
    check_count_changes_each_cycle: assert property (
        @(posedge clk) disable iff (!reset)
        1'b1 |=> (count != $past(count))
    );

endmodule