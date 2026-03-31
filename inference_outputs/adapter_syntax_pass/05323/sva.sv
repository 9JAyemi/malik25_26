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

    localparam logic [Width-1:0] INIT = {Width{1'bx}};

    // Reset forces Count to the initial value.
    check_reset_value: assert property (
        @(posedge Clock) Reset |-> (Count == INIT)
    );

    // Load updates Count with In on the next cycle.
    check_load_updates_count: assert property (
        @(posedge Clock) disable iff (Reset)
        Load |=> (Count == $past(In))
    );

    // Load has priority over Enable.
    check_load_overrides_enable: assert property (
        @(posedge Clock) disable iff (Reset)
        (Load && Enable) |=> (Count == $past(In))
    );

    // Enable increments Count when Load is low.
    check_enable_increments_count: assert property (
        @(posedge Clock) disable iff (Reset)
        (!Load && Enable && !Limited && !Down) |=> (Count == ($past(Count) + 1'b1))
    );

    // Enable decrements Count when Load is low and Down is high.
    check_enable_decrements_count: assert property (
        @(posedge Clock) disable iff (Reset)
        (!Load && Enable && !Limited && Down) |=> (Count == ($past(Count) - 1'b1))
    );

    // Limited mode stops incrementing at the maximum value.
    check_limited_mode_stops_increment: assert property (
        @(posedge Clock) disable iff (Reset)
        (!Load && Enable && Limited && !Down && (Count == {Width{1'b1}})) |=> (Count == {Width{1'b1}})
    );

    // Limited mode stops decrementing at zero.
    check_limited_mode_stops_decrement: assert property (
        @(posedge Clock) disable iff (Reset)
        (!Load && Enable && Limited && Down && (Count == {Width{1'b0}})) |=> (Count == {Width{1'b0}})
    );

    // Count holds when no load or enable condition is active.
    check_count_holds_when_idle: assert property (
        @(posedge Clock) disable iff (Reset)
        (!Load && !Enable) |=> (Count == $past(Count))
    );

endmodule

module Register_sva #(
    parameter int Width = 32,
    parameter bit AsyncReset = 0,
    parameter bit AsyncSet = 0
) (
    input logic Clock,
    input logic Reset,
    input logic Set,
    input logic Enable,
    input logic [Width-1:0] In,
    input logic [Width-1:0] Out
);

    localparam logic [Width-1:0] INIT = {Width{1'bx}};

    // Reset forces Out to the initial value.
    check_reset_value: assert property (
        @(posedge Clock) Reset |-> (Out == INIT)
    );

    // Enable updates Out with In on the next cycle.
    check_enable_updates_out: assert property (
        @(posedge Clock) disable iff (Reset)
        Enable |=> (Out == $past(In))
    );

    // Out holds when Enable is low.
    check_out_holds_when_idle: assert property (
        @(posedge Clock) disable iff (Reset)
        !Enable |=> (Out == $past(Out))
    );

endmodule