module sky130_fd_sc_hd__lpflow_inputiso0n_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic SLEEP_B
);

// X must equal A AND SLEEP_B.
    check_function_equivalence: assert property (
        @(posedge clk) X == (A & SLEEP_B)
    );

// When SLEEP_B is LOW, X must be LOW.
    check_sleep_forces_low: assert property (
        @(posedge clk) !SLEEP_B |-> (X == 1'b0)
    );

// When A is LOW, X must be LOW.
    check_a_low_forces_low: assert property (
        @(posedge clk) !A |-> (X == 1'b0)
    );

// When both A and SLEEP_B are HIGH, X must be HIGH.
    check_both_high_drive_high: assert property (
        @(posedge clk) (A && SLEEP_B) |-> (X == 1'b1)
    );

// A HIGH X requires both A and SLEEP_B to be HIGH.
    check_high_output_requires_both_high: assert property (
        @(posedge clk) X |-> (A && SLEEP_B)
    );

endmodule
