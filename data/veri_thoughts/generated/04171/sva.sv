module sky130_fd_sc_hdll__inputiso0n_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic SLEEP_B
);

    // When sleep is asserted low, the output is forced low.
    check_sleep_forces_zero: assert property (
        @(posedge clk) (SLEEP_B == 1'b0) |-> (X == 1'b0)
    );

    // When sleep is deasserted high, the output passes input A.
    check_awake_passes_input: assert property (
        @(posedge clk) (SLEEP_B == 1'b1) |-> (X == A)
    );

    // A high output requires both A and SLEEP_B to be high.
    check_high_output_requires_both_high: assert property (
        @(posedge clk) (X == 1'b1) |-> ((A == 1'b1) && (SLEEP_B == 1'b1))
    );

    // The output implements the AND of A and SLEEP_B.
    check_and_function: assert property (
        @(posedge clk) X == (A & SLEEP_B)
    );

endmodule