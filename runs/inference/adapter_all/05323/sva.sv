module Counter_sva #(
    parameter int Width = 32,
    parameter bit Limited = 0,
    parameter bit Down = 0,
    parameter bit AsyncReset = 0,
    parameter bit AsyncSet = 0
) (
    input logic Clock,
    input logic Reset,
    input logic Set,
    input logic Load,
    input logic Enable,
    input logic [Width-1:0] In,
    input logic [Width-1:0] Count
);

    // Reset loads the counter to the initial value.
    check_reset_loads_initial: assert property (
        @(posedge Clock) Reset |=> (Count == {Width{1'b0}})
    );

    // Load updates the counter with In on the next cycle.
    check_load_updates_count: assert property (
        @(posedge Clock) disable iff (Reset)
        Load |=> (Count == $past(In))
    );

    // Enable updates the counter with the next value on the next cycle.
    check_enable_updates_count: assert property (
        @(posedge Clock) disable iff (Reset)
        (!Load && Enable) |=> (Count == ($past(Down) ? ($past(Count) - 1) : ($past(Count) + 1)))
    );

    // Without load or enable, the counter holds its value.
    check_hold_when_idle: assert property (
        @(posedge Clock) disable iff (Reset)
        (!Load && !Enable) |=> (Count == $past(Count))
    );

    // In down mode, the counter decrements when enabled.
    check_down_mode_decrements: assert property (
        @(posedge Clock) disable iff (Reset)
        (!Load && Enable && Down) |=> (Count == ($past(Count) - 1))
    );

    // In up mode, the counter increments when enabled.
    check_up_mode_increments: assert property (
        @(posedge Clock) disable iff (Reset)
        (!Load && Enable && !Down) |=> (Count == ($past(Count) + 1))
    );

    // In down mode, decrementing from zero wraps to all ones.
    check_down_wraparound: assert property (
        @(posedge Clock) disable iff (Reset)
        (!Load && Enable && Down && (Count == {Width{1'b0}})) |=> (Count == {Width{1'b1}})
    );

    // In up mode, incrementing from all ones wraps to zero.
    check_up_wraparound: assert property (
        @(posedge Clock) disable iff (Reset)
        (!Load && Enable && !Down && (Count == {Width{1'b1}})) |=> (Count == {Width{1'b0}})
    );

endmodule