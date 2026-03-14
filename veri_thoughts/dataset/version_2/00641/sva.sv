module sky130_fd_sc_lp__inputiso0p_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic SLEEP
);
    // X implements A & ~SLEEP
    check_function_equivalence: assert property (
        @(posedge clk) X == (A & ~SLEEP)
    );

    // When SLEEP is high, X must be 0
    check_isolation_when_sleep: assert property (
        @(posedge clk) SLEEP |-> (X == 1'b0)
    );

    // When SLEEP is low, X equals A
    check_transparent_when_awake: assert property (
        @(posedge clk) !SLEEP |-> (X == A)
    );

    // X high only if A is high and SLEEP is low
    check_x_high_conditions: assert property (
        @(posedge clk) (X == 1'b1) |-> (A == 1'b1) && (SLEEP == 1'b0)
    );

    // If A is low, X must be low
    check_a_low_forces_x_low: assert property (
        @(posedge clk) (A == 1'b0) |-> (X == 1'b0)
    );

    // If A is high, X equals ~SLEEP
    check_a_high_sets_x_to_not_sleep: assert property (
        @(posedge clk) (A == 1'b1) |-> (X == ~SLEEP)
    );

    // X can only rise when A is high and SLEEP is low
    check_x_rise_requires_a_and_awake: assert property (
        @(posedge clk) $rose(X) |-> (A == 1'b1) && (SLEEP == 1'b0)
    );

    // X can only fall when A is low or SLEEP is high
    check_x_fall_requires_a0_or_sleep1: assert property (
        @(posedge clk) $fell(X) |-> (A == 1'b0) || (SLEEP == 1'b1)
    );

    // On SLEEP rising edge, X must be 0
    check_x_zero_on_sleep_rise: assert property (
        @(posedge clk) $rose(SLEEP) |-> (X == 1'b0)
    );

    // On SLEEP falling edge with A high, X must be 1
    check_x_one_on_sleep_fall_if_a_high: assert property (
        @(posedge clk) ($fell(SLEEP) && (A == 1'b1)) |-> (X == 1'b1)
    );

    // On A rising edge with SLEEP low, X must be 1
    check_x_one_on_a_rise_if_awake: assert property (
        @(posedge clk) ($rose(A) && (SLEEP == 1'b0)) |-> (X == 1'b1)
    );

    // On A falling edge with SLEEP low, X must be 0
    check_x_zero_on_a_fall_if_awake: assert property (
        @(posedge clk) ($fell(A) && (SLEEP == 1'b0)) |-> (X == 1'b0)
    );
endmodule