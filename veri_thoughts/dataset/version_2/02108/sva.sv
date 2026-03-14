module sky130_fd_sc_ms__a21bo_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1_N
);
    // X implements (~B1_N) | (A1 & A2).
    check_function_equivalence: assert property (
        @(posedge clk) disable iff (1'b0) X == ((~B1_N) | (A1 & A2))
    );

    // B1_N low forces X high.
    check_b1n_low_forces_x_high: assert property (
        @(posedge clk) disable iff (1'b0) (B1_N == 1'b0) |-> (X == 1'b1)
    );

    // With B1_N high, X equals A1 & A2.
    check_b1n_high_equals_and: assert property (
        @(posedge clk) disable iff (1'b0) (B1_N == 1'b1) |-> (X == (A1 & A2))
    );

    // X low implies B1_N high and not (A1 & A2).
    check_x_low_implication: assert property (
        @(posedge clk) disable iff (1'b0) (X == 1'b0) |-> ((B1_N == 1'b1) && !(A1 && A2))
    );

    // If B1_N high and X high, then both A1 and A2 are high.
    check_b1n_high_x_high_implies_both_as_high: assert property (
        @(posedge clk) disable iff (1'b0) ((B1_N == 1'b1) && (X == 1'b1)) |-> ((A1 == 1'b1) && (A2 == 1'b1))
    );

    // A1 & A2 high guarantees X high.
    check_and_true_sets_x_high: assert property (
        @(posedge clk) disable iff (1'b0) ((A1 == 1'b1) && (A2 == 1'b1)) |-> (X == 1'b1)
    );

    // Both A1 and A2 low makes X equal ~B1_N.
    check_both_as_low_x_eq_not_b1n: assert property (
        @(posedge clk) disable iff (1'b0) ((A1 == 1'b0) && (A2 == 1'b0)) |-> (X == (~B1_N))
    );

    // With B1_N high and A1 low, X must be low.
    check_b1n_high_a1_low_clears_x: assert property (
        @(posedge clk) disable iff (1'b0) ((B1_N == 1'b1) && (A1 == 1'b0)) |-> (X == 1'b0)
    );

    // With B1_N high and A2 low, X must be low.
    check_b1n_high_a2_low_clears_x: assert property (
        @(posedge clk) disable iff (1'b0) ((B1_N == 1'b1) && (A2 == 1'b0)) |-> (X == 1'b0)
    );

    // X high implies (~B1_N) or (A1 & A2).
    check_x_high_implication: assert property (
        @(posedge clk) disable iff (1'b0) (X == 1'b1) |-> ((~B1_N) | (A1 & A2))
    );
endmodule