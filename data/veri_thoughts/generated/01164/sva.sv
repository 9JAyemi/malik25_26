module sky130_fd_sc_lp__isobufsrc_sva (
    input logic clk,
    input logic X,
    input logic SLEEP,
    input logic A
);
    // Functional equivalence: X = ~SLEEP & A.
    check_functional_equivalence: assert property (
        @(posedge clk) X == ((!SLEEP) && A)
    );

    // SLEEP high forces X low.
    check_sleep_forces_zero: assert property (
        @(posedge clk) SLEEP |-> (X == 1'b0)
    );

    // When not sleeping, X passes A.
    check_awake_pass_through: assert property (
        @(posedge clk) !SLEEP |-> (X == A)
    );

    // X high implies A high and SLEEP low.
    check_x_high_implies_inputs: assert property (
        @(posedge clk) (X == 1'b1) |-> (!SLEEP && (A == 1'b1))
    );

    // A low forces X low.
    check_a_zero_implies_x_zero: assert property (
        @(posedge clk) (A == 1'b0) |-> (X == 1'b0)
    );

    // Rising SLEEP immediately forces X low.
    check_sleep_rise_forces_low: assert property (
        @(posedge clk) $rose(SLEEP) |-> (X == 1'b0)
    );

    // Falling SLEEP makes X follow A.
    check_sleep_fall_pass_through: assert property (
        @(posedge clk) $fell(SLEEP) |-> (X == A)
    );

    // While awake across cycles, a change on A causes a change on X.
    check_awake_a_change_causes_x_change: assert property (
        @(posedge clk) (!SLEEP && !$past(SLEEP) && $changed(A)) |-> $changed(X)
    );

    // While sleeping across cycles, X stays 0 and does not change on A changes.
    check_sleep_stable_zero: assert property (
        @(posedge clk) (SLEEP && $past(SLEEP) && $changed(A)) |-> (X == 1'b0) && !$changed(X)
    );

    // X rising requires A=1 and SLEEP=0.
    check_x_rise_implies_inputs: assert property (
        @(posedge clk) $rose(X) |-> (!SLEEP && (A == 1'b1))
    );

    // X falling requires A=0 or SLEEP=1.
    check_x_fall_implies_cause: assert property (
        @(posedge clk) $fell(X) |-> ((A == 1'b0) || (SLEEP == 1'b1))
    );
endmodule