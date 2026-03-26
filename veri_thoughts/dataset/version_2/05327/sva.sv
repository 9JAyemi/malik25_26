module sky130_fd_sc_lp__inputiso1n_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic SLEEP_B
);

    // X must implement A OR not SLEEP_B.
    check_output_matches_or_function: assert property (
        @(posedge clk) X == (A | ~SLEEP_B)
    );

    // When awake, X must pass A.
    check_awake_mode_passes_input: assert property (
        @(posedge clk) SLEEP_B |-> (X == A)
    );

    // When sleep is asserted low, X must be forced high.
    check_sleep_mode_forces_high: assert property (
        @(posedge clk) !SLEEP_B |-> (X == 1'b1)
    );

    // A high must force X high.
    check_high_input_forces_high_output: assert property (
        @(posedge clk) A |-> (X == 1'b1)
    );

    // The only low-output case is A low while awake.
    check_low_output_case: assert property (
        @(posedge clk) (!A && SLEEP_B) |-> (X == 1'b0)
    );

endmodule