module sky130_fd_sc_hdll__or3b_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic B,
    input logic C_N
);

    // X must equal A OR B OR inverted C_N.
    check_output_matches_or3b_function: assert property (
        @(posedge clk) X == (A | B | (~C_N))
    );

    // A asserted must drive X high.
    check_a_high_forces_x_high: assert property (
        @(posedge clk) (A == 1'b1) |-> (X == 1'b1)
    );

    // B asserted must drive X high.
    check_b_high_forces_x_high: assert property (
        @(posedge clk) (B == 1'b1) |-> (X == 1'b1)
    );

    // Active-low C input asserted low must drive X high.
    check_cn_low_forces_x_high: assert property (
        @(posedge clk) (C_N == 1'b0) |-> (X == 1'b1)
    );

    // With A and B low, X must follow the inversion of C_N.
    check_ab_low_makes_x_follow_inverted_cn: assert property (
        @(posedge clk) ((A == 1'b0) && (B == 1'b0)) |-> (X == (~C_N))
    );

    // When all OR terms are inactive, X must be low.
    check_all_inputs_inactive_force_x_low: assert property (
        @(posedge clk) ((A == 1'b0) && (B == 1'b0) && (C_N == 1'b1)) |-> (X == 1'b0)
    );

endmodule