module sky130_fd_sc_ms__a21bo_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1_N
);

    // Purely combinational RTL; assertions are sampled on the formal global clock.
    
    // X matches the implemented NAND/NAND/BUF logic.
    check_functional_equivalence: assert property (
        @($global_clock) X == ~(B1_N & ~(A1 & A2))
    );

    // A low B1_N forces the final NAND output high.
    check_b1n_low_forces_x_high: assert property (
        @($global_clock) ~B1_N |-> X
    );

    // High A1 and A2 force X high.
    check_a1_a2_high_force_x_high: assert property (
        @($global_clock) (A1 & A2) |-> X
    );

    // With B1_N high, if A1 and A2 are not both high then X is low.
    check_b1n_high_and_not_a1a2_forces_x_low: assert property (
        @($global_clock) (B1_N & ~(A1 & A2)) |-> ~X
    );

    // If X is high while B1_N is high, both A1 and A2 must be high.
    check_x_high_with_b1n_high_requires_a1_a2_high: assert property (
        @($global_clock) (X & B1_N) |-> (A1 & A2)
    );

    // A low X can only occur when B1_N is high and at least one A input is low.
    check_x_low_characterization: assert property (
        @($global_clock) ~X |-> (B1_N & (~A1 | ~A2))
    );

endmodule