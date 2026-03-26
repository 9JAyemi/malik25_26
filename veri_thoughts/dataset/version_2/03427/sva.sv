module sky130_fd_sc_lp__iso1n_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic SLEEP_B
);

    // X must match the implemented OR-of-A and inverted SLEEP_B.
    check_function_equation: assert property (
        @(posedge clk) X == (A | ~SLEEP_B)
    );

    // When not sleeping, X must pass A through.
    check_pass_through_when_awake: assert property (
        @(posedge clk) SLEEP_B |-> (X == A)
    );

    // When sleeping, X must be clamped high.
    check_clamp_high_when_sleep: assert property (
        @(posedge clk) !SLEEP_B |-> (X == 1'b1)
    );

endmodule