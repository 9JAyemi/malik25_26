module sky130_fd_sc_lp__iso1n_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic SLEEP_B
);

    // X implements A OR not SLEEP_B.
    check_iso_function: assert property (
        @(posedge clk) X == (A | ~SLEEP_B)
    );

    // When awake, X follows A.
    check_transparent_when_awake: assert property (
        @(posedge clk) SLEEP_B |-> (X == A)
    );

    // When sleeping, X is forced high.
    check_clamped_high_when_sleeping: assert property (
        @(posedge clk) !SLEEP_B |-> X
    );

    // A high input always forces X high.
    check_high_input_forces_high_output: assert property (
        @(posedge clk) A |-> X
    );

    // X can be low only when awake and A is low.
    check_low_output_only_for_awake_low_input: assert property (
        @(posedge clk) !X |-> (SLEEP_B && !A)
    );

    // Awake with a low input must produce a low output.
    check_awake_low_input_produces_low_output: assert property (
        @(posedge clk) (SLEEP_B && !A) |-> !X
    );

endmodule