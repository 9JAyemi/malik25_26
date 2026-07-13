module up_down_counter_sva (
    input logic clk,
    input logic up_down,
    input logic load,
    input logic reset,
    input logic [3:0] count,
    input logic [3:0] data_in
);
    // Reset drives count to zero on the next clock.
    reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 4'b0000)
    );

    // Load captures data_in on the next clock when not in reset.
    load_captures_data: assert property (
        @(posedge clk) disable iff (reset) load |=> (count == $past(data_in))
    );

    // When not loading and up_down=1, count increments by 1 on the next clock.
    increment_when_up: assert property (
        @(posedge clk) disable iff (reset) (!load && up_down) |=> (count == $past(count) + 4'd1)
    );

    // When not loading and up_down=0, count decrements by 1 on the next clock.
    decrement_when_down: assert property (
        @(posedge clk) disable iff (reset) (!load && !up_down) |=> (count == $past(count) - 4'd1)
    );

    // With no load and no direction specified (both 0), count holds its value.
    hold_when_idle: assert property (
        @(posedge clk) disable iff (reset) (!load && !up_down) |=> (count == $past(count))
    );

    // With no load and both directions asserted (both 1), count holds its value.
    hold_when_both_high: assert property (
        @(posedge clk) disable iff (reset) (!load && up_down && !up_down) |=> (count == $past(count))
    );

    // With no load and both directions deasserted (both 0), count holds its value.
    hold_when_both_low: assert property (
        @(posedge clk) disable iff (reset) (!load && !up_down && !up_down) |=> (count == $past(count))
    );

    // Incrementing from 4'hF wraps to 4'h0 on the next clock.
    increment_wraparound: assert property (
        @(posedge clk) disable iff (reset) (!load && up_down && (count == 4'hF)) |=> (count == 4'h0)
    );

    // Decrementing from 4'h0 wraps to 4'hF on the next clock.
    decrement_wraparound: assert property (
        @(posedge clk) disable iff (reset) (!load && !up_down && (count == 4'h0)) |=> (count == 4'hF)
    );

    // Load has priority over direction when both are asserted.
    load_priority_over_direction: assert property (
        @(posedge clk) disable iff (reset) (load && up_down && !up_down) |=> (count == $past(data_in))
    );
endmodule