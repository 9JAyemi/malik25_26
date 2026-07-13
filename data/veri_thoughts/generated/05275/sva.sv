module Register_sva #(
    parameter int Width = 32,
    parameter AsyncReset = 0,
    parameter AsyncSet = 0,
    parameter [Width-1:0] ResetValue = {Width{1'b0}},
    parameter [Width-1:0] SetValue = {Width{1'b1}}
)(
    input logic Clock,
    input logic Reset,
    input logic Set,
    input logic Enable,
    input logic [Width-1:0] In,
    input logic [Width-1:0] Out
);

    // Low Reset with AsyncReset enabled loads ResetValue.
    check_asyncreset_low_loads_reset_value: assert property (
        @(posedge Clock) disable iff ($initstate)
        $past(AsyncReset && !Reset) |-> (Out == ResetValue)
    );

    // Set loads SetValue unless low-active AsyncReset took priority.
    check_set_loads_set_value: assert property (
        @(posedge Clock) disable iff ($initstate || $past(AsyncReset && !Reset))
        $past(Set) |-> (Out == SetValue)
    );

    // Reset high without Set loads ResetValue.
    check_reset_high_loads_reset_value: assert property (
        @(posedge Clock) disable iff ($initstate)
        $past(Reset && !Set) |-> (Out == ResetValue)
    );

    // Enable loads In when Set and Reset are low.
    check_enable_loads_input: assert property (
        @(posedge Clock) disable iff ($initstate || $past(AsyncReset && !Reset))
        $past(!Reset && !Set && Enable) |-> (Out == $past(In))
    );

    // No active control holds the previous value.
    check_no_control_holds_value: assert property (
        @(posedge Clock) disable iff ($initstate || $past(AsyncReset && !Reset))
        $past(!Reset && !Set && !Enable) |-> (Out == $past(Out))
    );

    // Set has priority over Reset when both are high.
    check_set_priority_over_reset: assert property (
        @(posedge Clock) disable iff ($initstate || $past(AsyncReset && !Reset))
        $past(Reset && Set) |-> (Out == SetValue)
    );

endmodule