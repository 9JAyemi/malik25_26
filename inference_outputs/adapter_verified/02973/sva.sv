module up_down_counter_sva (
    input logic clk,
    input logic reset,
    input logic load,
    input logic up_down,
    input logic [3:0] count
);

// Reset clears the counter on the next cycle.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 4'b0000)
    );

// Load captures the current count value.
    check_load_captures_count: assert property (
        @(posedge clk) disable iff (reset)
        load |=> (count == $past(count))
    );

// Up mode increments the counter by one.
    check_up_mode_increments: assert property (
        @(posedge clk) disable iff (reset)
        (!load && up_down) |=> (count == ($past(count) + 4'b0001))
    );

// Down mode decrements the counter by one.
    check_down_mode_decrements: assert property (
        @(posedge clk) disable iff (reset)
        (!load && !up_down) |=> (count == ($past(count) - 4'b0001))
    );

// When not loading, the counter follows the selected direction.
    check_count_update_without_load: assert property (
        @(posedge clk) disable iff (reset)
        !load |=> (count == ($past(count) + (up_down ? 4'b0001 : 4'b0001) - (up_down ? 4'b0000 : 4'b0001)))
    );

// The 4-bit counter wraps from 15 to 0 in up mode.
    check_up_wraparound: assert property (
        @(posedge clk) disable iff (reset)
        (!load && up_down && (count == 4'hF)) |=> (count == 4'h0)
    );

// The 4-bit counter wraps from 0 to 15 in down mode.
    check_down_wraparound: assert property (
        @(posedge clk) disable iff (reset)
        (!load && !up_down && (count == 4'h0)) |=> (count == 4'hF)
    );

endmodule
