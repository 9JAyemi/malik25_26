module up_down_counter_assertions (
    input logic       clk,
    input logic       load,
    input logic       up_down,
    input logic [3:0] count
);

    // Load clears the counter to zero.
    check_load_clears_count: assert property (
        @(posedge clk) load |=> (count == 4'b0000)
    );

    // The counter increments when load is low and up_down is high.
    check_count_increments: assert property (
        @(posedge clk) (!load && up_down) |=> (count == ($past(count) + 4'd1))
    );

    // The counter decrements when load is low and up_down is low.
    check_count_decrements: assert property (
        @(posedge clk) (!load && !up_down) |=> (count == ($past(count) - 4'd1))
    );

    // Load has priority over the direction control.
    check_load_priority: assert property (
        @(posedge clk) (load && up_down) |=> (count == 4'b0000)
    );

    // Increment wraps from 15 back to 0.
    check_increment_wraps_from_max: assert property (
        @(posedge clk) (!load && up_down && (count == 4'hF)) |=> (count == 4'h0)
    );

    // Decrement wraps from 0 down to 15.
    check_decrement_wraps_from_zero: assert property (
        @(posedge clk) (!load && !up_down && (count == 4'h0)) |=> (count == 4'hF)
    );

endmodule