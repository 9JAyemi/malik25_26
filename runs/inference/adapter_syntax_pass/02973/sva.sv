module up_down_counter_sva (
    input logic clk,
    input logic reset,
    input logic load,
    input logic up_down,
    input logic [3:0] count
);

    // Reset clears the counter on the next clock.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 4'h0)
    );

    // Load holds the previous count value.
    check_load_holds_count: assert property (
        @(posedge clk) disable iff (reset)
        load |=> (count == $past(count))
    );

    // Up mode increments the counter by one.
    check_up_increments_count: assert property (
        @(posedge clk) disable iff (reset)
        (!load && up_down) |=> (count == ($past(count) + 4'h1))
    );

    // Down mode decrements the counter by one.
    check_down_decrements_count: assert property (
        @(posedge clk) disable iff (reset)
        (!load && !up_down) |=> (count == ($past(count) - 4'h1))
    );

    // The counter value never exceeds 4'hF.
    check_count_within_range: assert property (
        @(posedge clk) disable iff (reset)
        (count <= 4'hF)
    );

endmodule