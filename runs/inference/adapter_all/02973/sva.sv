module up_down_counter_sva (
    input logic clk,
    input logic reset,
    input logic load,
    input logic up_down,
    input logic [3:0] count
);

    // Reset clears the counter on the next clock.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 4'b0000)
    );

    // Load holds the current count value.
    check_load_holds_count: assert property (
        @(posedge clk) disable iff (reset)
        load |=> (count == $past(count))
    );

    // Up mode increments the counter when not loading.
    check_up_mode_increments_count: assert property (
        @(posedge clk) disable iff (reset)
        (!load && up_down) |=> (count == ($past(count) + 4'b0001))
    );

    // Down mode decrements the counter when not loading.
    check_down_mode_decrements_count: assert property (
        @(posedge clk) disable iff (reset)
        (!load && !up_down) |=> (count == ($past(count) - 4'b0001))
    );

    // Incrementing from 4'hF wraps to 4'h0.
    check_up_wraparound: assert property (
        @(posedge clk) disable iff (reset)
        (!load && up_down && (count == 4'hF)) |=> (count == 4'h0)
    );

    // Decrementing from 4'h0 wraps to 4'hF.
    check_down_wraparound: assert property (
        @(posedge clk) disable iff (reset)
        (!load && !up_down && (count == 4'h0)) |=> (count == 4'hF)
    );

endmodule