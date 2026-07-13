module up_counter_sva #(parameter SIZE = 4) (
    input logic            Clock,
    input logic            Reset,
    input logic            Enable,
    input logic            Load,
    input logic [SIZE-1:0] Data,
    input logic [SIZE-1:0] Q
);

    // A reset observed on a clock edge leaves the counter cleared by the next clock.
    reset_clears_counter: assert property (
        @(posedge Clock) Reset |=> (Q == {SIZE{1'b0}})
    );

    // Load causes Q to capture Data on the next clock.
    load_captures_data: assert property (
        @(posedge Clock) disable iff (Reset)
        Load |=> (Q == $past(Data))
    );

    // Load has priority over Enable when both are asserted.
    load_has_priority_over_enable: assert property (
        @(posedge Clock) disable iff (Reset)
        (Load && Enable) |=> (Q == $past(Data))
    );

    // Enable increments Q when Load is low.
    increment_when_enabled: assert property (
        @(posedge Clock) disable iff (Reset)
        (!Load && Enable) |=> (Q == ($past(Q) + 1'b1))
    );

    // Q holds its value when neither Load nor Enable is asserted.
    hold_when_idle: assert property (
        @(posedge Clock) disable iff (Reset)
        (!Load && !Enable) |=> (Q == $past(Q))
    );

    // Incrementing from the maximum value wraps Q to zero.
    wrap_from_max_to_zero: assert property (
        @(posedge Clock) disable iff (Reset)
        (!Load && Enable && (Q == {SIZE{1'b1}})) |=> (Q == {SIZE{1'b0}})
    );

endmodule