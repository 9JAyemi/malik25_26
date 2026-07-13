module sky130_fd_sc_hvl__lsbuflv2hv_clkiso_hlkg_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic SLEEP_B
);

    // X must equal A gated by SLEEP_B.
    check_x_matches_gated_input: assert property (
        @(posedge clk) X == (SLEEP_B & A)
    );

    // When SLEEP_B is low, X must be low.
    check_sleep_low_forces_x_low: assert property (
        @(posedge clk) !SLEEP_B |-> !X
    );

    // When SLEEP_B is high, X must equal A.
    check_sleep_high_passes_a: assert property (
        @(posedge clk) SLEEP_B |-> (X == A)
    );

    // A high X requires SLEEP_B to be high.
    check_x_high_requires_sleep_high: assert property (
        @(posedge clk) X |-> SLEEP_B
    );

    // A high X requires A to be high.
    check_x_high_requires_a_high: assert property (
        @(posedge clk) X |-> A
    );

endmodule