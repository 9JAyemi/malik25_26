module sky130_fd_sc_hd__lpflow_inputiso0n_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic SLEEP_B
);

    // X must equal the AND of A and SLEEP_B.
    check_x_matches_and_function: assert property (
        @(posedge clk) X == (A & SLEEP_B)
    );

    // When SLEEP_B is low, X must be low.
    check_sleep_low_forces_x_low: assert property (
        @(posedge clk) !SLEEP_B |-> !X
    );

    // When A is low, X must be low.
    check_a_low_forces_x_low: assert property (
        @(posedge clk) !A |-> !X
    );

    // When both inputs are high, X must be high.
    check_both_inputs_high_drive_x_high: assert property (
        @(posedge clk) (A && SLEEP_B) |-> X
    );

    // A high X requires both inputs to be high.
    check_x_high_requires_both_inputs_high: assert property (
        @(posedge clk) X |-> (A && SLEEP_B)
    );

endmodule