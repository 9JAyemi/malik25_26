module ClockDivider_sva #(parameter Hz = 27000000) (
    input logic        clock,
    input logic        reset,
    input logic        fastMode,
    input logic        oneHertz_enable,
    input logic [24:0] counter
);

    // A reset cycle clears the counter and deasserts the pulse by the next clock.
    check_reset_clears_state: assert property (
        @(posedge clock) reset |=> (counter == 25'd0 && oneHertz_enable == 1'b0)
    );

    // In fast mode, reaching count 3 produces a pulse and reloads the counter.
    check_fastmode_terminal_pulse: assert property (
        @(posedge clock) disable iff (reset)
        (fastMode && (counter == 25'd3)) |=> (counter == 25'd0 && oneHertz_enable == 1'b1)
    );

    // In normal mode, reaching count Hz produces a pulse and reloads the counter.
    check_normal_terminal_pulse: assert property (
        @(posedge clock) disable iff (reset)
        (!fastMode && (counter == Hz)) |=> (counter == 25'd0 && oneHertz_enable == 1'b1)
    );

    // In fast mode, non-terminal counts increment and keep the pulse low.
    check_fastmode_increment: assert property (
        @(posedge clock) disable iff (reset)
        (fastMode && (counter != 25'd3)) |=> (counter == ($past(counter) + 25'd1) && oneHertz_enable == 1'b0)
    );

    // In normal mode, non-terminal counts increment and keep the pulse low.
    check_normal_increment: assert property (
        @(posedge clock) disable iff (reset)
        (!fastMode && (counter != Hz)) |=> (counter == ($past(counter) + 25'd1) && oneHertz_enable == 1'b0)
    );

    // Whenever the pulse is high, the counter state is zero.
    check_enable_implies_zero_counter: assert property (
        @(posedge clock) disable iff (reset)
        oneHertz_enable |-> (counter == 25'd0)
    );

    // A pulse lasts one cycle and counting restarts from zero on the next cycle.
    check_pulse_single_cycle_and_restart: assert property (
        @(posedge clock) disable iff (reset)
        oneHertz_enable |=> (counter == 25'd1 && oneHertz_enable == 1'b0)
    );

endmodule