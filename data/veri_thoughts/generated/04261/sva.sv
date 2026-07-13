module sky130_fd_sc_lp__inputiso0n_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic SLEEP_B
);

    // X must always equal the AND of A and SLEEP_B.
    check_and_function: assert property (
        @(posedge clk) X == (A & SLEEP_B)
    );

    // When SLEEP_B is low, X must be forced low.
    check_sleep_low_clamps_output: assert property (
        @(posedge clk) (SLEEP_B == 1'b0) |-> (X == 1'b0)
    );

    // When SLEEP_B is high, X must match A.
    check_sleep_high_passes_input: assert property (
        @(posedge clk) (SLEEP_B == 1'b1) |-> (X == A)
    );

    // A high output requires both A and SLEEP_B to be high.
    check_output_high_requires_both_inputs: assert property (
        @(posedge clk) (X == 1'b1) |-> ((A == 1'b1) && (SLEEP_B == 1'b1))
    );

endmodule