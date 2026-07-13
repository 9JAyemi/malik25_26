module up_down_counter_sva (
    input logic clk,
    input logic up_down,
    input logic load,
    input logic reset,
    input logic [3:0] count,
    input logic [3:0] data_in
);

// Reset drives count to zero on the next clock.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 4'b0000)
    );

// Load captures data_in into count when not in reset.
    check_load_captures_data: assert property (
        @(posedge clk) disable iff (reset)
        load |=> (count == $past(data_in))
    );

// Up-count increments count by one when load is low.
    check_up_count_increments: assert property (
        @(posedge clk) disable iff (reset)
        (!load && up_down) |=> (count == ($past(count) + 4'd1))
    );

// Down-count decrements count by one when load is low.
    check_down_count_decrements: assert property (
        @(posedge clk) disable iff (reset)
        (!load && !up_down) |=> (count == ($past(count) - 4'd1))
    );

// Count holds its value when no control is asserted.
    check_hold_when_idle: assert property (
        @(posedge clk) disable iff (reset)
        (!load && !up_down && !reset) |=> (count == $past(count))
    );

endmodule
