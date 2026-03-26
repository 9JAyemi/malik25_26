module Counter_sva #(
    parameter integer Width = 32,
    parameter Limited = 0,
    parameter Down = 0,
    parameter [Width-1:0] Initial = {Width{1'bx}},
    parameter AsyncReset = 0,
    parameter AsyncSet = 0
) (
    input logic Clock,
    input logic Reset,
    input logic Set,
    input logic Load,
    input logic Enable,
    input logic [Width-1:0] In,
    input logic [Width-1:0] Count
);

    // Mixed combinational/sequential logic; Clock is the state clock and Reset is active high.
    // Set is unused in this RTL.

    // Reset drives Count to Initial.
    check_reset_sets_initial: assert property (
        @(posedge Clock) Reset |-> (Count === Initial)
    );

    // Load has priority and updates Count with In on the next clock.
    check_load_captures_in: assert property (
        @(posedge Clock) disable iff (Reset)
        Load |=> (Count === $past(In))
    );

    // Up-count mode increments when enabled and not blocked by the limit.
    check_up_count_increments: assert property (
        @(posedge Clock) disable iff (Reset)
        (!Down && !Load && Enable && (!Limited || !(&Count))) |=> (Count === ($past(Count) + 1'b1))
    );

    // Down-count mode decrements when enabled and not blocked by the limit.
    check_down_count_decrements: assert property (
        @(posedge Clock) disable iff (Reset)
        (Down && !Load && Enable && (!Limited || (Count != {Width{1'b0}}))) |=> (Count === ($past(Count) - 1'b1))
    );

    // With no load and no enable, Count holds its value.
    check_hold_when_disabled: assert property (
        @(posedge Clock) disable iff (Reset)
        (!Load && !Enable) |=> (Count === $past(Count))
    );

    // In limited up-count mode, Count holds at all ones.
    check_hold_at_up_limit: assert property (
        @(posedge Clock) disable iff (Reset)
        (Limited && !Down && !Load && Enable && (&Count)) |=> (Count === $past(Count))
    );

    // In limited down-count mode, Count holds at zero.
    check_hold_at_down_limit: assert property (
        @(posedge Clock) disable iff (Reset)
        (Limited && Down && !Load && Enable && (Count == {Width{1'b0}})) |=> (Count === $past(Count))
    );

endmodule

module Register_sva #(
    parameter integer Width = 32,
    parameter [Width-1:0] Initial = {Width{1'bx}},
    parameter AsyncReset = 0,
    parameter AsyncSet = 0
) (
    input logic Clock,
    input logic Reset,
    input logic Set,
    input logic Enable,
    input logic [Width-1:0] In,
    input logic [Width-1:0] Out
);

    // Sequential logic; Clock is the state clock and Reset is active high.
    // Set is unused in this RTL.

    // Reset drives Out to Initial.
    check_reset_sets_initial: assert property (
        @(posedge Clock) Reset |-> (Out === Initial)
    );

    // Enable captures In on the next clock.
    check_enable_captures_in: assert property (
        @(posedge Clock) disable iff (Reset)
        Enable |=> (Out === $past(In))
    );

    // When not enabled, Out holds its value.
    check_hold_when_disabled: assert property (
        @(posedge Clock) disable iff (Reset)
        !Enable |=> (Out === $past(Out))
    );

endmodule