module up_down_counter_sva (
    input logic clk,
    input logic load,
    input logic up_down,
    input logic [2:0] out
);

// Load clears the counter on the next cycle.
    check_load_clears_counter: assert property (
        @(posedge clk) load |=> (out == 3'b000)
    );

// Up mode increments the counter when load is low.
    check_up_mode_increments: assert property (
        @(posedge clk) (!load && up_down) |=> (out == ($past(out) + 3'd1))
    );

// Down mode decrements the counter when load is low.
    check_down_mode_decrements: assert property (
        @(posedge clk) (!load && !up_down) |=> (out == ($past(out) - 3'd1))
    );

// The counter holds its value when neither control is asserted.
    check_hold_when_idle: assert property (
        @(posedge clk) (!load && !up_down) |=> (out == $past(out))
    );

// Load has priority over up/down when both are asserted.
    check_load_priority_over_up_down: assert property (
        @(posedge clk) (load && up_down) |=> (out == 3'b000)
    );

// Increment wraps from 7 to 0 in up mode.
    check_wrap_up_from_max: assert property (
        @(posedge clk) (!load && up_down && (out == 3'b111)) |=> (out == 3'b000)
    );

// Decrement wraps from 0 to 7 in down mode.
    check_wrap_down_from_zero: assert property (
        @(posedge clk) (!load && !up_down && (out == 3'b000)) |=> (out == 3'b111)
    );

endmodule
