module sky130_fd_sc_hvl__lsbuflv2hv_clkiso_hlkg_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic SLEEP_B
);

    // Output must be the AND of A and SLEEP_B.
    check_output_function: assert property (
        @(posedge clk) X == (A & SLEEP_B)
    );

    // Low SLEEP_B must force X low.
    check_sleep_low_forces_zero: assert property (
        @(posedge clk) !SLEEP_B |-> !X
    );

    // When enabled, X must match A.
    check_enabled_output_follows_input: assert property (
        @(posedge clk) SLEEP_B |-> (X == A)
    );

    // A high X requires both A and SLEEP_B high.
    check_output_high_requires_enable_and_input: assert property (
        @(posedge clk) X |-> (A && SLEEP_B)
    );

    // A low input must force X low.
    check_low_input_forces_zero: assert property (
        @(posedge clk) !A |-> !X
    );

endmodule