module sky130_fd_sc_lp__iso0p_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic SLEEP
);

// X must equal A & ~SLEEP.
    check_function_equivalence: assert property (
        @(posedge clk) X == (A & ~SLEEP)
    );

// When SLEEP is LOW, X must be LOW.
    check_sleep_forces_low: assert property (
        @(posedge clk) (SLEEP == 1'b0) |-> (X == 1'b0)
    );

// When SLEEP is HIGH, X must equal A.
    check_awake_passes_a: assert property (
        @(posedge clk) (SLEEP == 1'b1) |-> (X == A)
    );

// A LOW forces X LOW regardless of SLEEP.
    check_a_low_forces_x_low: assert property (
        @(posedge clk) (A == 1'b0) |-> (X == 1'b0)
    );

// A HIGH with SLEEP HIGH drives X HIGH.
    check_awake_a_high_drives_x_high: assert property (
        @(posedge clk) (A == 1'b1 && SLEEP == 1'b1) |-> (X == 1'b1)
    );

// A HIGH with SLEEP LOW drives X LOW.
    check_sleep_a_high_drives_x_low: assert property (
        @(posedge clk) (A == 1'b1 && SLEEP == 1'b0) |-> (X == 1'b0)
    );

// X HIGH implies A is HIGH and SLEEP is HIGH.
    check_x_high_implies_awake_and_a_high: assert property (
        @(posedge clk) (X == 1'b1) |-> (A == 1'b1 && SLEEP == 1'b1)
    );

// X LOW implies A is LOW or SLEEP is LOW.
    check_x_low_implies_a_low_or_sleep_low: assert property (
        @(posedge clk) (X == 1'b0) |-> (A == 1'b0 || SLEEP == 1'b0)
    );

endmodule
