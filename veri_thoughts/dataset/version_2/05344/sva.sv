module sky130_fd_sc_lp__iso0n_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic SLEEP_B
);

    // X must equal the AND of A and SLEEP_B.
    check_x_matches_and: assert property (
        @(posedge clk) X == (A & SLEEP_B)
    );

    // X must be low when isolation is active.
    check_x_low_when_sleep_b_low: assert property (
        @(posedge clk) !SLEEP_B |-> (X == 1'b0)
    );

    // X must be low when A is low.
    check_x_low_when_a_low: assert property (
        @(posedge clk) !A |-> (X == 1'b0)
    );

    // X must be high when both inputs are high.
    check_x_high_when_both_inputs_high: assert property (
        @(posedge clk) (A && SLEEP_B) |-> (X == 1'b1)
    );

    // A high X requires both inputs to be high.
    check_x_high_requires_both_inputs: assert property (
        @(posedge clk) X |-> (A && SLEEP_B)
    );

endmodule