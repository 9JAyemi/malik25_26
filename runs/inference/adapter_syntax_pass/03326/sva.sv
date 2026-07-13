module sky130_fd_sc_hdll__or4bb_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic B,
    input logic C_N,
    input logic D_N
);

    // X matches the implemented OR-of-three function.
    check_x_matches_implemented_function: assert property (
        @(posedge clk) X == (A | B | ~(C_N & D_N))
    );

    // A high forces X high.
    check_a_high_forces_x_high: assert property (
        @(posedge clk) A |-> X
    );

    // B high forces X high.
    check_b_high_forces_x_high: assert property (
        @(posedge clk) B |-> X
    );

    // Both C_N and D_N high force X high.
    check_c_n_and_d_n_high_force_x_high: assert property (
        @(posedge clk) (C_N & D_N) |-> X
    );

    // With A and B low, X reduces to the NAND of C_N and D_N.
    check_ab_low_reduces_to_c_n_and_d_n_nand: assert property (
        @(posedge clk) (!A && !B) |-> (X == ~(C_N & D_N))
    );

    // With A and C_N high, X reduces to B OR the inverted D_N.
    check_a_and_c_n_high_reduces_to_b_or_not_d_n: assert property (
        @(posedge clk) (A && C_N) |-> (X == (B | ~D_N))
    );

    // With A and D_N high, X reduces to B OR the inverted C_N.
    check_a_and_d_n_high_reduces_to_b_or_not_c_n: assert property (
        @(posedge clk) (A && D_N) |-> (X == (B | ~C_N))
    );

    // With B and C_N high, X reduces to A OR the inverted D_N.
    check_b_and_c_n_high_reduces_to_a_or_not_d_n: assert property (
        @(posedge clk) (B && C_N) |-> (X == (A | ~D_N))
    );

    // With B and D_N high, X reduces to A OR the inverted C_N.
    check_b_and_d_n_high_reduces_to_a_or_not_c_n: assert property (
        @(posedge clk) (B && D_N) |-> (X == (A | ~C_N))
    );

    // With A, B, and C_N high, X reduces to the inverted D_N.
    check_a_b_and_c_n_high_reduces_to_not_d_n: assert property (
        @(posedge clk) (A && B && C_N) |-> (X == ~D_N)
    );

    // With A, B, and D_N high, X reduces to the inverted C_N.
    check_a_b_and_d_n_high_reduces_to_not_c_n: assert property (
        @(posedge clk) (A && B && D_N) |-> (X == ~C_N)
    );

endmodule