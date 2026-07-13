module and_gate_sva (
    input logic A,
    input logic B,
    input logic clk,
    input logic reset,   // Active-high synchronous reset
    input logic X
);

    // When previous cycle was not reset, X equals previous A & B.
    check_next_matches_prev_and: assert property (
        @(posedge clk) disable iff (reset || $initstate) !$past(reset) |-> (X == $past(A & B))
    );

    // If previous cycle was reset, X must be 0 now.
    reset_prev_cycle_forces_zero: assert property (
        @(posedge clk) disable iff ($initstate) $past(reset) |-> (X == 1'b0)
    );

    // If reset is asserted now, X must be 0 on the next cycle.
    reset_now_forces_zero_next: assert property (
        @(posedge clk) disable iff ($initstate) reset |-> (X == 1'b0)
    );

    // While reset stays asserted across cycles, X must be 0.
    hold_zero_during_continuous_reset: assert property (
        @(posedge clk) disable iff ($initstate) (reset && $past(reset)) |-> (X == 1'b0)
    );

    // If prev A=1 and prev B=1 and not in reset prev cycle, X must be 1 now.
    prev_inputs_both_one_yield_one: assert property (
        @(posedge clk) disable iff (reset || $initstate) (!$past(reset) && $past(A) && $past(B)) |-> (X == 1'b1)
    );

    // If either prev A=0 or prev B=0 and not in reset prev cycle, X must be 0 now.
    prev_input_zero_yields_zero: assert property (
        @(posedge clk) disable iff (reset || $initstate) (!$past(reset) && (!$past(A) || !$past(B))) |-> (X == 1'b0)
    );

    // If X is 1 now and not in reset prev cycle, then both prev A and prev B were 1.
    x_one_requires_prev_inputs_one: assert property (
        @(posedge clk) disable iff (reset || $initstate) (!$past(reset) && (X == 1'b1)) |-> ($past(A) && $past(B))
    );

    // If X is 0 now and not in reset prev cycle, then at least one of prev A or prev B was 0.
    x_zero_requires_prev_input_zero: assert property (
        @(posedge clk) disable iff (reset || $initstate) (!$past(reset) && (X == 1'b0)) |-> (!$past(A) || !$past(B))
    );

    // On falling edge of reset, X must be 0 in this cycle.
    x_zero_on_reset_fall: assert property (
        @(posedge clk) disable iff ($initstate) $fell(reset) |-> (X == 1'b0)
    );

endmodule