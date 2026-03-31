module sky130_fd_sc_hdll__or4bb_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic B,
    input logic C_N,
    input logic D_N
);

    // X matches the implemented OR-of-terms function.
    check_x_matches_function: assert property (
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

    // Both C_N and D_N low force X high.
    check_c_n_low_and_d_n_low_force_x_high: assert property (
        @(posedge clk) (!C_N && !D_N) |-> X
    );

    // With A and B low, X reduces to the NAND term.
    check_ab_low_reduces_to_nand_term: assert property (
        @(posedge clk) (!A && !B) |-> (X == ~(C_N & D_N))
    );

    // With C_N and D_N high, X reduces to the OR of A and B.
    check_c_n_high_and_d_n_high_reduces_to_or: assert property (
        @(posedge clk) (C_N && D_N) |-> (X == (A | B))
    );

    // With A and B low and C_N high, X reduces to the inverse NAND term.
    check_ab_low_c_n_high_reduces_to_inverse_nand: assert property (
        @(posedge clk) (!A && !B && C_N) |-> (X == ~D_N)
    );

    // With A and B low and D_N high, X reduces to the inverse NAND term.
    check_ab_low_d_n_high_reduces_to_inverse_nand: assert property (
        @(posedge clk) (!A && !B && D_N) |-> (X == ~C_N)
    );

    // With A and B low, X equals the NAND of C_N and D_N.
    check_ab_low_equals_nand_term: assert property (
        @(posedge clk) (!A && !B) |-> (X == ~(C_N & D_N))
    );

    // With C_N and D_N high, X equals the OR of A and B.
    check_c_n_high_d_n_high_equals_or: assert property (
        @(posedge clk) (C_N && D_N) |-> (X == (A | B))
    );

    // With A and B low, X equals the inverse NAND of C_N and D_N.
    check_ab_low_equals_inverse_nand: assert property (
        @(posedge clk) (!A && !B) |-> (X == ~D_N | ~C_N)
    );

endmodule