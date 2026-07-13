module Counter_sva (
    input logic        Clock,
    input logic        Reset,
    input logic        Set,
    input logic        Load,
    input logic        Enable,
    input logic [31:0] In,
    input logic [31:0] Count
);

// Reset drives Count to 32'hx on the next cycle.
    check_reset_clears_count: assert property (
        @(posedge Clock) Reset |=> (Count == 32'hx)
    );

// Load captures In on the next cycle when Enable is low.
    check_load_captures_in: assert property (
        @(posedge Clock) disable iff (Reset)
        (Load && !Enable) |=> (Count == $past(In))
    );

// Load has priority over Enable when both are high.
    check_load_priority_over_enable: assert property (
        @(posedge Clock) disable iff (Reset)
        (Load && Enable) |=> (Count == $past(In))
    );

// Enable increments Count by one when Load is low.
    check_increment_when_enabled: assert property (
        @(posedge Clock) disable iff (Reset)
        (!Load && Enable) |=> (Count == ($past(Count) + 32'd1))
    );

// Count holds its value when neither Load nor Enable is high.
    check_hold_when_idle: assert property (
        @(posedge Clock) disable iff (Reset)
        (!Load && !Enable) |=> (Count == $past(Count))
    );

// Count wraps from 32'hFFFF_FFFF to 0 when incrementing.
    check_increment_wrap: assert property (
        @(posedge Clock) disable iff (Reset)
        (!Load && Enable && (Count == 32'hFFFF_FFFF)) |=> (Count == 32'd0)
    );

// Count becomes 0 when Load is high and In is 0.
    check_load_zero: assert property (
        @(posedge Clock) disable iff (Reset)
        (Load && (In == 32'd0)) |=> (Count == 32'd0)
    );

// Count becomes 1 when Load is high and In is 1.
    check_load_one: assert property (
        @(posedge Clock) disable iff (Reset)
        (Load && (In == 32'd1)) |=> (Count == 32'd1)
    );

endmodule
